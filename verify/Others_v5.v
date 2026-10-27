(* TM28 and TM27: one shared accelerated checker, with the stronger
   complete-return macros used for both blank initial states.
   TM28 is written in its direct mirror; TM27 retains its original code.
   Only BusyCoq and the standard library are required. *)
From BusyCoq Require Import Individual62 ES_v3 FastRev Permute.
Require Import String List Bool NArith Lia.
Set Implicit Arguments.
Open Scope sym.

Module SharedDeck.
Section Deck.
Context {letter:Type}.
Record deck := Deck { front:list letter; back:list letter; weight:N }.
Definition contents x := front x++rev(back x).
Definition empty := Deck [] [] 0%N.
Definition flip x := Deck (back x) (front x) (weight x).
Definition push c x := Deck (front x) (c::back x) (N.succ(weight x)).
Definition map_letters (f:letter->letter) x :=
  Deck (map f(front x)) (map f(back x)) (weight x).
Fixpoint halves_aux (slow fast acc:list letter) := match slow with
  | []=>(fast_rev acc,[])
  | a::slow'=>match fast with
    | _::_::fast'=>halves_aux slow' fast'(a::acc)
    | _=>(fast_rev acc,slow) end end.
Definition halves xs := halves_aux xs xs [].
Definition pop x := match front x with
  | c::f=>Some(c,Deck f (back x) (N.pred(weight x)))
  | []=>let '(b,f):=halves(back x) in match fast_rev f with
    | c::f=>Some(c,Deck f b(N.pred(weight x)))
    | []=>match fast_rev b with []=>None
      | c::f=>Some(c,Deck f [] (N.pred(weight x))) end end end.
Definition join x y := if N.leb(weight x)(weight y)
  then Deck (front x++fast_rev_append(back x)(front y)) (back y)
       (N.add(weight x)(weight y))
  else Deck (front x) (back y++fast_rev_append(front y)(back x))
       (N.add(weight x)(weight y)).
Lemma flip_spec x : contents(flip x)=rev(contents x).
Proof. destruct x; cbn; rewrite rev_app_distr,rev_involutive; reflexivity. Qed.
Lemma push_spec c x : contents(push c x)=contents x++[c].
Proof. destruct x; cbn; apply app_assoc. Qed.
Lemma map_spec f x : contents(map_letters f x)=map f(contents x).
Proof. destruct x; cbn; rewrite map_app,map_rev; reflexivity. Qed.
Lemma halves_aux_spec slow fast acc :
  let '(a,b):=halves_aux slow fast acc in a++b=rev acc++slow.
Proof.
  revert fast acc; induction slow as [|a slow IH]; intros fast acc.
  - cbn[halves_aux]; rewrite fast_rev_spec; reflexivity.
  - destruct fast as [|b [|c fast]]; cbn[halves_aux];
      try(rewrite fast_rev_spec; reflexivity).
    specialize(IH fast(a::acc)); destruct(halves_aux slow fast(a::acc))as [x y].
    rewrite IH; cbn[rev]; rewrite <-app_assoc; reflexivity.
Qed.
Lemma halves_spec xs : let '(a,b):=halves xs in a++b=xs.
Proof. exact(halves_aux_spec xs xs []). Qed.
Lemma pop_spec x : match pop x with None=>contents x=[]
  | Some(c,y)=>contents x=c::contents y end.
Proof.
  destruct x as [[|c f]b k]; unfold pop,contents; cbn[front back weight].
  - pose proof(halves_spec b)as H; unfold halves in *.
    destruct(halves_aux b b [])as [g h]eqn:E; cbn in H; rewrite <-H,rev_app_distr.
    rewrite !fast_rev_spec; destruct(rev h)as [|c f]; cbn[app].
    + destruct(rev g); unfold contents; cbn[front back]; rewrite ?app_nil_r; reflexivity.
    + reflexivity.
  - reflexivity.
Qed.
Lemma join_spec x y : contents(join x y)=contents x++contents y.
Proof.
  destruct x as [f b k],y as [g c j]; unfold join; cbn[front back weight].
  destruct(N.leb k j); unfold contents; cbn[front back];
    rewrite !fast_rev_append_spec,?rev_app_distr,?rev_involutive,!app_assoc;
    reflexivity.
Qed.
End Deck.
End SharedDeck.

(* Both stacks are nearest-cut first.  R reads the first right cell, L the
   first left cell.  A token implementation supplies only exact stream
   operations; neither grammar reachability nor heuristic weight is trusted. *)
Module DirectedChecker.
Section Checker.
Context {token:Type}.
Variable tm:TM.
Variable denote:dir->list token->side.
Variable pop:dir->list token->Sym*list token.
Variable push:dir->Sym->list token->list token.
Hypothesis empty_spec : forall d, denote d []=0inf.
Hypothesis pop_spec : forall d s,
  denote d s=fst(pop d s) >> denote d(snd(pop d s)).
Hypothesis push_spec : forall d b s, denote d(push d b s)=b >> denote d s.

Inductive config := Cfg (q:Q)(d:dir)(l r:list token).
Definition decode c := match c with Cfg q d l r=>match d with
  | L=>denote L l <{{q}} denote R r | R=>denote L l {{q}}> denote R r end end.
Definition raw c := match c with
  | Cfg q L l r=>let '(b,l'):=pop L l in match tm(q,b) with
    | None=>None | Some(w,L,q')=>Some(Cfg q' L l'(push R w r))
    | Some(w,R,q')=>Some(Cfg q' R(push L w l')r) end
  | Cfg q R l r=>let '(b,r'):=pop R r in match tm(q,b) with
    | None=>None | Some(w,L,q')=>Some(Cfg q' L l(push R w r'))
    | Some(w,R,q')=>Some(Cfg q' R(push L w l)r') end end.
Definition transfer c o := match o with
  | None=>halts tm(decode c)
  | Some c'=>halts tm(decode c')->halts tm(decode c) end.
Lemma raw_spec c : transfer c(raw c).
Proof.
  destruct c as [q [|]l r]; unfold raw; cbn[decode].
  - pose proof(pop_spec L l)as H; destruct(pop L l)as [b l']; cbn[fst snd]in H.
    unfold transfer; cbn[decode]; rewrite H; cbn[hd tl].
    destruct(tm(q,b))as [[[w d]q']|]eqn:E.
    + destruct d; cbn[decode]; rewrite push_spec; intro K;
        eapply halts_evstep; [exact K|apply progress_evstep,progress_base|
          exact K|apply progress_evstep,progress_base].
      * exact(@step_left tm q q' b w(denote L l')(denote R r)E).
      * exact(@step_right tm q q' b w(denote L l')(denote R r)E).
    + apply halted_halts; exact E.
  - pose proof(pop_spec R r)as H; destruct(pop R r)as [b r']; cbn[fst snd]in H.
    unfold transfer; cbn[decode]; rewrite H; cbn[hd tl].
    destruct(tm(q,b))as [[[w d]q']|]eqn:E.
    + destruct d; cbn[decode]; rewrite push_spec; intro K;
        eapply halts_evstep; [exact K|apply progress_evstep,progress_base|
          exact K|apply progress_evstep,progress_base].
      * exact(@step_left tm q q' b w(denote L l)(denote R r')E).
      * exact(@step_right tm q q' b w(denote L l)(denote R r')E).
    + apply halted_halts; exact E.
Qed.

Variable macro:config->option config.
Hypothesis macro_spec : forall c c', macro c=Some c' -> decode c -[tm]->* decode c'.
Definition advance c := match macro c with Some c'=>Some c' | None=>raw c end.
Lemma advance_spec c : transfer c(advance c).
Proof.
  unfold advance; destruct(macro c)as [c'|]eqn:E; [|apply raw_spec].
  unfold transfer; intro H; eapply halts_evstep; [exact H|apply macro_spec,E].
Qed.
Definition chain (o:option config)(f:config->option config) :=
  match o with None=>None | Some c=>f c end.
Fixpoint iterate_pos n c := match n with
  | xH=>advance c
  | xO n=>chain(iterate_pos n c)(iterate_pos n)
  | xI n=>chain(chain(iterate_pos n c)(iterate_pos n))advance end.
Definition iterate n c := match n with N0=>Some c | Npos p=>iterate_pos p c end.
Definition check n q := match iterate n(Cfg q R [] []) with None=>true | _=>false end.
Lemma chain_spec c o f : transfer c o -> (forall x,transfer x(f x)) ->
  transfer c(chain o f).
Proof.
  destruct o as [x|]; cbn[chain transfer]; auto.
  intros H K; specialize(K x); destruct(f x); cbn[transfer]in *; tauto.
Qed.
Lemma iterate_pos_spec n c : transfer c(iterate_pos n c).
Proof.
  revert c; induction n; intro c; cbn[iterate_pos].
  - apply chain_spec; [apply chain_spec; apply IHn|apply advance_spec].
  - apply chain_spec; apply IHn.
  - apply advance_spec.
Qed.
Lemma check_spec n q : check n q=true -> halts tm(0inf {{q}}> 0inf).
Proof.
  assert(H:transfer(Cfg q R [] [])(iterate n(Cfg q R [] []))).
  { destruct n; cbn[iterate transfer]; [trivial|apply iterate_pos_spec]. }
  unfold check; destruct(iterate n(Cfg q R [] [])); [discriminate|].
  intro E; cbn[transfer decode]in H; rewrite !empty_spec in H; exact H.
Qed.
End Checker.
End DirectedChecker.

Module TM28.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA1LD_1RA0RC_0LE---_0LF1LF_0LA0RB").

Notation hR := (C,[]).
Notation hE := (E,[]).
Notation hD := (D,[]).
Notation hF := (F,[]).

Inductive letter := Star | Zero | One.
Definition swap x := match x with Star=>Star | Zero=>One | One=>Zero end.
Definition W x : list Sym := match x with
  | Star=>[0;1;1] | Zero=>[0;1;0;1;1] | One=>[0;1;1;1;1] end.
Definition V x : list Sym := match x with
  | Star=>[1;0;0] | Zero=>[1;0;1;0;0] | One=>[1;0;0;0;0] end.
Definition Ws := flat_map W.
Definition Vs := flat_map V.
Definition swaps := map swap.
Lemma forward_word x : segRR tm hR hR (W x) (rev(V x)).
Proof. destruct x; unfold W,V,segRR; intros; esx. Qed.
Lemma backward_word x : segLL tm hE hE (rev(V x)) (W(swap x)).
Proof. destruct x; unfold W,V,swap,segLL; intros; esx. Qed.

Lemma forward_words xs : segRR tm hR hR (Ws xs) (rev(Vs xs)).
Proof.
  induction xs as [|x xs IH]; [intros l r; apply evstep_refl|].
  intros l r; cbn[Ws Vs flat_map]; rewrite rev_app_distr,!Str_app_assoc.
  eapply evstep_trans; [apply forward_word|apply IH].
Qed.
Lemma backward_words xs : segLL tm hE hE (rev(Vs xs)) (Ws(swaps xs)).
Proof.
  induction xs as [|x xs IH]; [intros l r; apply evstep_refl|].
  intros l r; cbn[Ws Vs swaps flat_map map]; rewrite rev_app_distr,!Str_app_assoc.
  eapply evstep_trans; [apply IH|apply backward_word].
Qed.

Definition digit (b:bool) : list Sym := if b then
  [1;0;1;0;1;0;1;0;0;1;0;0;0;0] else
  [1;0;0;0;0;0;0;0;0;1;0;1;0;0].
Definition carry_word : list Sym := [0;1;1;1;1;1;1;1;1;0;1;0;1;1].
Lemma digit_stop : segLR tm hE hR (rev(digit false)) (rev(digit true)).
Proof. unfold segLR,digit; intros; esx. Qed.
Lemma digit_carry : segLL tm hE hE (rev(digit true)) carry_word.
Proof. unfold segLL,digit,carry_word; intros; esx. Qed.
Lemma digit_return : segRR tm hR hR carry_word (rev(digit false)).
Proof. unfold segRR,digit,carry_word; intros; esx. Qed.

(* Fixed-capacity binary counter, least-significant digit nearest the head.
   None is overflow, not an implicit extra zero and not a halt result. *)
Fixpoint increment bs := match bs with
  | []=>None
  | false::bs=>Some(true::bs)
  | true::bs=>match increment bs with
      None=>None | Some bs'=>Some(false::bs') end end.
Definition left_digits := flat_map (fun b=>rev(digit b)).
Lemma increment_spec bs bs' : increment bs=Some bs' ->
  segLR tm hE hR (left_digits bs) (left_digits bs').
Proof.
  revert bs'; induction bs as [|b bs IH]; intros bs' H; [discriminate|].
  destruct b; cbn[increment] in H.
  - destruct(increment bs) as [t|] eqn:E; [|discriminate].
    injection H as <-; specialize(IH t eq_refl).
    intros l r; cbn[left_digits flat_map]; rewrite !Str_app_assoc.
    eapply evstep_trans; [apply digit_carry|].
    eapply evstep_trans; [apply IH|apply digit_return].
  - injection H as <-; intros l r; cbn[left_digits flat_map].
    rewrite !Str_app_assoc; apply digit_stop.
Qed.

Definition Q4 : list Sym := [0;1;1;1;1;1;1;1;1].
Definition Z4 : list Sym := [1;0;0;0;0;0;0;0;0].
Definition Z4' : list Sym := [1;0;1;0;1;0;1;0;0].
Lemma q4_forward : segRR tm hR hR Q4 (rev Z4).
Proof. unfold segRR,Q4,Z4; intros; esx. Qed.
Lemma q4_repeat : segLR tm hE hR (rev Z4) (rev Z4').
Proof. unfold segLR,Z4,Z4'; intros; esx. Qed.
Lemma q4_return : segLL tm hE hE (rev Z4') Q4.
Proof. unfold segLL,Z4',Q4; intros; esx. Qed.
Lemma q2_return : segRL tm hR hD (W One++[0;0]) [1;1;0;0;0;1;1].
Proof. unfold segRL,W; intros; esx. Qed.
Lemma star_return : segRL tm hR hE (W Star++[0;0]) (W One).
Proof. unfold segRL,W; intros; esx. Qed.
Definition bridge_in : list Sym := [0;1;1;1;1;1;1;0;0].
Definition bridge_out : list Sym := [0;1;0;1;0;0;1;0;0].
Definition bridge_back : list Sym := [0;0;1;1;1;1;0;1;1].
Lemma bridge_forward : segRR tm hR hR bridge_in (rev bridge_out).
Proof. unfold segRR,bridge_in,bridge_out; intros; esx. Qed.
Lemma bridge_return : segLL tm hE hF (rev bridge_out) bridge_back.
Proof. unfold segLL,bridge_out,bridge_back; intros; esx. Qed.
Lemma bridge_return_D : segLL tm hD hF (rev bridge_out) bridge_back.
Proof. unfold segLL,bridge_out,bridge_back; intros; esx. Qed.
Definition bridge_back_F : list Sym := [0;0;1;1;1;1;1;1;0].
Lemma bridge_return_F : segLL tm hF hF (rev bridge_out) bridge_back_F.
Proof. unfold segLL,bridge_out,bridge_back_F; intros; esx. Qed.
Lemma bridge_restart : forall l r,
  l <* rev(V One) <{{F}} bridge_back *> r -[tm]->*
  l <* rev([0]++V Zero++V One++V Star) {{C}}> r.
Proof. intros; unfold V,bridge_back; esx. Qed.
Module Checker.
Definition deck := @SharedDeck.deck letter.
Definition actual (x:bool) a := if x then swap a else a.
Definition word (p:bool) x a := if p then V(actual x a) else W(actual x a).
Definition dword d p x a := match d with
  | L=>fast_rev(word p x a) | R=>word p x a end.
Definition bits d p x z := flat_map(dword d p x)(SharedDeck.contents z).
Inductive token := Bit (b:Sym) | Band (p x:bool)(z:deck)
  | Count (bs:list bool) | Carry (n:nat).
Definition token_bits d u := match u with
  | Bit b=>[b] | Band p x z=>bits d p x z
  | Count bs=>left_digits bs | Carry n=>carry_word^^n end.
Definition denote d s := flat_map(token_bits d)s *> 0inf.
Definition prepend bs s := map Bit bs++s.
Definition push (d:dir) b s := match b,s with 0,[]=>[] | _,_=>Bit b::s end.
Definition empty_deck := @SharedDeck.empty letter.
Definition deck_empty (z:deck) := match SharedDeck.front z,SharedDeck.back z with
  | [],[]=>true | _,_=>false end.
Definition put_band p x z s := if deck_empty z then s else
  match s with Band q y w::s' => if Bool.eqb p q then
    if Bool.eqb x y then Band p x(SharedDeck.join z w)::s'
    else if N.leb(SharedDeck.weight z)(SharedDeck.weight w)
      then Band p y(SharedDeck.join(SharedDeck.map_letters swap z)w)::s'
      else Band p x(SharedDeck.join z(SharedDeck.map_letters swap w))::s'
    else Band p x z::s
  | _=>Band p x z::s end.
Definition put_count bs s := match bs with []=>s | _=>match s with
  | Count cs::s'=>Count(bs++cs)::s' | _=>Count bs::s end end.
Definition put_carry n s := match n with O=>s | _=>match s with
  | Carry m::s'=>Carry(n+m)::s' | _=>Carry n::s end end.
Fixpoint pop d s := match s with
  | []=>(0,[])
  | Bit b::s=>(b,s)
  | Count []::s=>pop d s
  | Count(b::bs)::s=>match rev(digit b) with
      []=>pop d s | c::cs=>(c,prepend cs(put_count bs s)) end
  | Carry O::s=>pop d s
  | Carry(S n)::s=>(0,prepend [1;1;1;1;1;1;1;1;0;1;0;1;1](put_carry n s))
  | Band p x z::s=>match SharedDeck.pop z with
      None=>pop d s | Some(a,w)=>match dword d p x a with
        []=>pop d s | b::bs=>(b,prepend bs(put_band p x w s)) end end end.
Fixpoint strip bs d s := match bs with []=>Some s | b::bs=>
  let '(c,t):=pop d s in if Eqb.eqb b c then strip bs d t else None end.

Lemma denote_empty d : denote d []=0inf.
Proof. reflexivity. Qed.
Lemma denote_bit d b s : denote d(Bit b::s)=b >> denote d s.
Proof. reflexivity. Qed.
Lemma denote_band d p x z s : denote d(Band p x z::s)=bits d p x z *> denote d s.
Proof. unfold denote; cbn[flat_map token_bits]; apply Str_app_assoc. Qed.
Lemma denote_count d bs s : denote d(Count bs::s)=left_digits bs *> denote d s.
Proof. unfold denote; cbn[flat_map token_bits]; apply Str_app_assoc. Qed.
Lemma denote_carry d n s : denote d(Carry n::s)=carry_word^^n *> denote d s.
Proof. unfold denote; cbn[flat_map token_bits]; apply Str_app_assoc. Qed.
Lemma push_spec d b s : denote d(push d b s)=b >> denote d s.
Proof. destruct b,s; try reflexivity; apply const_unfold. Qed.
Lemma prepend_spec d bs s : denote d(prepend bs s)=bs *> denote d s.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  change(denote d(Bit b::prepend bs s)=b >> (bs *> denote d s)).
  rewrite denote_bit,IH; reflexivity.
Qed.
Lemma bits_join d p x z w :
  bits d p x(SharedDeck.join z w)=bits d p x z++bits d p x w.
Proof. unfold bits; rewrite SharedDeck.join_spec,flat_map_app; reflexivity. Qed.
Lemma bits_map d p x z :
  bits d p x(SharedDeck.map_letters swap z)=bits d p(negb x)z.
Proof.
  unfold bits; rewrite SharedDeck.map_spec.
  generalize(SharedDeck.contents z); intro cs; induction cs as [|a cs IH]; [reflexivity|].
  cbn[flat_map map]; rewrite IH; f_equal; destruct a,x,p,d; reflexivity.
Qed.
Lemma bits_empty d p x z : deck_empty z=true -> bits d p x z=[].
Proof. destruct z as [[|a f][|b g]k]; cbn[deck_empty]; try discriminate; reflexivity. Qed.
Lemma put_band_spec d p x z s : denote d(put_band p x z s)=bits d p x z *> denote d s.
Proof.
  unfold put_band; destruct(deck_empty z)eqn:E.
  - rewrite(bits_empty d p x z E); reflexivity.
  - destruct s as [|[b|q y w|bs|n]s]; try apply denote_band.
    destruct(Bool.eqb p q)eqn:H; [apply Bool.eqb_prop in H; subst q|apply denote_band].
    destruct(Bool.eqb x y)eqn:K.
    + apply Bool.eqb_prop in K; subst y.
      rewrite !denote_band,bits_join,Str_app_assoc; reflexivity.
    + assert(Y:y=negb x) by (destruct x,y; cbn in K |- *; congruence).
      subst y; destruct(N.leb(SharedDeck.weight z)(SharedDeck.weight w));
        rewrite !denote_band,bits_join,bits_map,?Bool.negb_involutive,Str_app_assoc;
        reflexivity.
Qed.
Lemma put_count_spec d bs s : denote d(put_count bs s)=left_digits bs *> denote d s.
Proof.
  destruct bs as [|b bs]; [reflexivity|].
  destruct s as [|[c|p x z|cs|n]s]; try apply denote_count.
  unfold put_count; rewrite !denote_count; unfold left_digits.
  rewrite flat_map_app,Str_app_assoc; reflexivity.
Qed.
Lemma put_carry_spec d n s : denote d(put_carry n s)=carry_word^^n *> denote d s.
Proof.
  destruct n; [reflexivity|].
  destruct s as [|[b|p x z|bs|m]s]; try apply denote_carry.
  unfold put_carry; rewrite !denote_carry,lpow_add,Str_app_assoc; reflexivity.
Qed.
Lemma dword_nonempty d p x a : dword d p x a<>[].
Proof. destruct d,p,x,a; discriminate. Qed.
Lemma pop_spec d s : denote d s=fst(pop d s) >> denote d(snd(pop d s)).
Proof.
  induction s as [|[b|p x z|bs|n]s IH]; [apply const_unfold|reflexivity| | |].
  - pose proof(SharedDeck.pop_spec z)as E.
    cbn[pop]; destruct(SharedDeck.pop z)as [[a w]|]; cbn in E.
    + unfold denote at 1; cbn[flat_map token_bits]; unfold bits at 1.
      rewrite E; cbn[flat_map]; rewrite !Str_app_assoc.
      destruct(dword d p x a)as [|b bs]eqn:H.
      * exfalso; exact(dword_nonempty d p x a H).
      * change(b >> (bs *> bits d p x w *> denote d s)=
          b >> denote d(prepend bs(put_band p x w s))).
        rewrite prepend_spec,put_band_spec; reflexivity.
    + unfold denote at 1; cbn[flat_map token_bits]; unfold bits.
      rewrite E; cbn[flat_map Str_app]; exact IH.
  - destruct bs as [|b bs]; [exact IH|].
    rewrite denote_count; cbn[left_digits flat_map]; rewrite Str_app_assoc.
    destruct b; cbn[pop digit rev app fst snd]; rewrite prepend_spec,put_count_spec; reflexivity.
  - destruct n; [exact IH|].
    rewrite denote_carry; cbn[lpow pop fst snd]; rewrite prepend_spec,put_carry_spec;
      unfold carry_word; reflexivity.
Qed.
Lemma strip_spec bs d s t : strip bs d s=Some t -> denote d s=bs *> denote d t.
Proof.
  revert s; induction bs as [|b bs IH]; intros s E; cbn[strip]in E.
  - injection E as <-; reflexivity.
  - pose proof(pop_spec d s)as H; destruct(pop d s)as [c u]; cbn[fst snd]in H.
    destruct b,c; cbn in E; try discriminate; rewrite H,(IH _ E); reflexivity.
Qed.

(* The finite recognizer tries the longest of the three actual columns. *)
Definition singleton a := SharedDeck.push a empty_deck.
Definition parse_band d p s := match strip(dword d p false Zero)d s with
    | Some t=>put_band p false(singleton Zero)t
    | None=>match strip(dword d p false One)d s with
      | Some t=>put_band p false(singleton One)t
      | None=>match strip(dword d p false Star)d s with
        | Some t=>put_band p false(singleton Star)t | None=>s end end end.
Definition prepare_band d p s := match s with Band _ _ _::_=>s | _=>parse_band d p s end.
Definition parse_count s := match strip(rev(digit false))L s with
  | Some t=>put_count[false]t | None=>
  match strip(rev(digit true))L s with Some t=>put_count[true]t | None=>s end end.
Definition prepare_count s := match s with Count _::_=>s | _=>parse_count s end.
Lemma bits_singleton d p x a : bits d p x(singleton a)=dword d p x a.
Proof. unfold bits,singleton; rewrite SharedDeck.push_spec; cbn; apply app_nil_r. Qed.
Lemma parse_band_spec d p s : denote d(parse_band d p s)=denote d s.
Proof.
  unfold parse_band.
  destruct(strip(dword d p false Zero)d s)as [t|]eqn:E.
  - rewrite put_band_spec,bits_singleton; symmetry; apply strip_spec,E.
  - destruct(strip(dword d p false One)d s)as [t|]eqn:F.
    + rewrite put_band_spec,bits_singleton; symmetry; apply strip_spec,F.
    + destruct(strip(dword d p false Star)d s)as [t|]eqn:G; [|reflexivity].
      rewrite put_band_spec,bits_singleton; symmetry; apply strip_spec,G.
Qed.
Lemma prepare_band_spec d p s : denote d(prepare_band d p s)=denote d s.
Proof. destruct s as [|[b|q x z|bs|n]s]; try reflexivity; apply parse_band_spec. Qed.
Lemma parse_count_spec s : denote L(parse_count s)=denote L s.
Proof.
  unfold parse_count; destruct(strip(rev(digit false))L s)as [t|]eqn:E.
  - rewrite put_count_spec; cbn[left_digits flat_map]; rewrite app_nil_r.
    symmetry; apply strip_spec,E.
  - destruct(strip(rev(digit true))L s)as [t|]eqn:F; [|reflexivity].
    rewrite put_count_spec; cbn[left_digits flat_map]; rewrite app_nil_r.
    symmetry; apply strip_spec,F.
Qed.
Lemma prepare_count_spec s : denote L(prepare_count s)=denote L s.
Proof. destruct s as [|[b|p x z|bs|n]s]; try reflexivity; apply parse_count_spec. Qed.

Lemma bits_R_W x z : bits R false x z=Ws(map(actual x)(SharedDeck.contents z)).
Proof.
  unfold bits; generalize(SharedDeck.contents z); intro cs; induction cs;
    cbn[flat_map map Ws dword word]; rewrite ?IHcs; reflexivity.
Qed.
Lemma bits_R_V x z : bits R true x z=Vs(map(actual x)(SharedDeck.contents z)).
Proof.
  unfold bits; generalize(SharedDeck.contents z); intro cs; induction cs;
    cbn[flat_map map Vs dword word]; rewrite ?IHcs; reflexivity.
Qed.
Lemma bits_flip p x z : bits L p x(SharedDeck.flip z)=rev(bits R p x z).
Proof.
  unfold bits; rewrite SharedDeck.flip_spec.
  generalize(SharedDeck.contents z); intro cs; induction cs as [|a cs IH]; [reflexivity|].
  cbn[rev]; rewrite flat_map_app; cbn[flat_map dword].
  rewrite fast_rev_spec,app_nil_r,IH,rev_app_distr; reflexivity.
Qed.
Lemma bits_L p x z : bits L p x z=rev(bits R p x(SharedDeck.flip z)).
Proof.
  replace z with (SharedDeck.flip(SharedDeck.flip z))at 1 by (destruct z; reflexivity).
  apply bits_flip.
Qed.
Lemma actual_swaps x cs : map(actual(negb x))cs=swaps(map(actual x)cs).
Proof.
  induction cs as [|a cs IH]; [reflexivity|].
  cbn[map swaps]; rewrite IH; f_equal; destruct x,a; reflexivity.
Qed.
Lemma overflow_spec bs : increment bs=None -> forall l r,
  l <* left_digits bs <{{E}} r -[tm]->*
  l <{{E}} carry_word^^length bs *> r.
Proof.
  induction bs as [|b bs IH]; intro H; intros l r; [apply evstep_refl|].
  destruct b; cbn[increment]in H; [|discriminate].
  destruct(increment bs)eqn:K; [discriminate|].
  specialize(IH eq_refl).
  cbn[left_digits flat_map length]; rewrite Str_app_assoc.
  eapply evstep_trans; [apply digit_carry|].
  cbn[lpow]; rewrite Str_app_assoc; rewrite <-lpow_shift'; apply IH.
Qed.
Lemma left_zero_digits n : left_digits(repeat false n)=(rev(digit false))^^n.
Proof. induction n; cbn[repeat left_digits flat_map lpow]; rewrite ?IHn; reflexivity. Qed.
Lemma carry_return_spec n : forall l r,
  l {{C}}> carry_word^^n *> r -[tm]->*
  l <* left_digits(repeat false n) {{C}}> r.
Proof.
  induction n as [|n IH]; intros l r; rewrite left_zero_digits; [apply evstep_refl|].
  cbn[lpow]; rewrite !Str_app_assoc.
  eapply evstep_trans; [apply digit_return|].
  rewrite <-lpow_shift'; rewrite left_zero_digits in IH; apply IH.
Qed.

Definition config := @DirectedChecker.config token.
Notation Cfg := DirectedChecker.Cfg.
Definition decode := @DirectedChecker.decode token denote.
Definition right_macro l r := match r with
  | Carry n::r'=>Some(Cfg C R(put_count(repeat false n)l)r')
  | _=>match prepare_band R false r with
    | Band false x z::r'=>Some(Cfg C R(put_band true x(SharedDeck.flip z)l)r')
    | _=>None end end.
Definition left_macro l r := match prepare_count l with
  | Count bs::l'=>match increment bs with
    | Some cs=>Some(Cfg C R(put_count cs l')r)
    | None=>Some(Cfg E L l'(put_carry(length bs)r)) end
  | _=>match prepare_band L true l with
    | Band true x z::l'=>Some(Cfg E L l'(put_band false(negb x)(SharedDeck.flip z)r))
    | _=>None end end.
Definition macro c := match c with
  | Cfg C R l r=>right_macro l r | Cfg E L l r=>left_macro l r | _=>None end.
Lemma right_macro_spec l r c : right_macro l r=Some c ->
  decode(Cfg C R l r) -[tm]->* decode c.
Proof.
  unfold right_macro; destruct r as [|[b|p x z|bs|n]r];
    try (intro H; injection H as <-; cbn[decode DirectedChecker.decode];
      rewrite denote_carry,put_count_spec; apply carry_return_spec).
  all: match goal with |- context[prepare_band ?d ?p ?s] =>
    pose proof(prepare_band_spec d p s)as H;
    destruct(prepare_band d p s)as [|[a|q y w|cs|m]r']eqn:K end;
    try discriminate.
  all: destruct q; try discriminate; intro T; injection T as <-;
    cbn[decode DirectedChecker.decode]; rewrite put_band_spec,bits_flip;
    rewrite denote_band in H; rewrite <-H,bits_R_W,bits_R_V; apply forward_words.
Qed.
Lemma left_macro_spec l r c : left_macro l r=Some c ->
  decode(Cfg E L l r) -[tm]->* decode c.
Proof.
  unfold left_macro; pose proof(prepare_count_spec l)as H.
  destruct(prepare_count l)as [|[b|p x z|bs|n]l']eqn:K.
  4: {
    destruct(increment bs)as [cs|]eqn:J; intro T; injection T as <-;
      cbn[decode DirectedChecker.decode]; rewrite denote_count in H; rewrite <-H.
    - rewrite put_count_spec; apply increment_spec,J.
    - rewrite put_carry_spec; apply overflow_spec,J.
  }
  all: pose proof(prepare_band_spec L true l)as HB;
    destruct(prepare_band L true l)as [|[a|q y w|cs|m]l'']eqn:KB; try discriminate.
  all: destruct q; try discriminate; intro T; injection T as <-;
    cbn[decode DirectedChecker.decode]; rewrite put_band_spec;
    rewrite denote_band in HB; rewrite <-HB,bits_L,bits_R_W,bits_R_V,actual_swaps;
    apply backward_words.
Qed.
Lemma macro_spec c c' : macro c=Some c' -> decode c -[tm]->* decode c'.
Proof. destruct c as [q d l r]; destruct q,d; cbn[macro]; try discriminate;
  [apply right_macro_spec|apply left_macro_spec]. Qed.
End Checker.


Module Actors.
Import Checker.
Notation Cfg := DirectedChecker.Cfg.
Inductive kernel := Q4Enter | Q3Enter | Q2Reflect | StarReflect
  | Q4Second | Q4Return | Q3E | Q3D | Q3F | V2FP.
Record packet := Packet { iq:Q; id:dir; il:list Sym; ir:list Sym;
  oq:Q; od:dir; ol:list Sym; orr:list Sym }.
Definition description k := match k with
  | Q4Enter=>Packet C R [] Q4 C R (rev Z4) []
  | Q3Enter=>Packet C R [] bridge_in C R (rev bridge_out) []
  | Q2Reflect=>Packet C R [] (W One++[0;0]) D L [] [1;1;0;0;0;1;1]
  | StarReflect=>Packet C R [] (W Star++[0;0]) E L [] (W One)
  | Q4Second=>Packet E L (rev Z4) [] C R (rev Z4') []
  | Q4Return=>Packet E L (rev Z4') [] E L [] Q4
  | Q3E=>Packet E L (rev bridge_out) [] F L [] bridge_back
  | Q3D=>Packet D L (rev bridge_out) [] F L [] bridge_back
  | Q3F=>Packet F L (rev bridge_out) [] F L [] bridge_back_F
  | V2FP=>Packet F L (rev(V One)) bridge_back C R
      (rev([0]++V Zero++V One++V Star)) [] end.
Definition plain (q:Q) d (l r:side) := match d with L=>l <{{q}} r | R=>l {{q}}> r end.
Lemma kernel_spec k l r :
  plain(iq(description k))(id(description k))(il(description k) *> l)(ir(description k) *> r)
  -[tm]->* plain(oq(description k))(od(description k))(ol(description k) *> l)(orr(description k) *> r).
Proof.
  destruct k; cbn[description iq id il ir oq od ol orr plain];
    try apply q4_forward; try apply bridge_forward;
    try(apply progress_evstep,q2_return); try(apply progress_evstep,star_return);
    try apply q4_repeat; try apply q4_return; try apply bridge_return;
    try apply bridge_return_D; try apply bridge_return_F; apply bridge_restart.
Qed.

Fixpoint literal_strip bs s := match bs with
  | []=>Some s
  | b::bs=>match s with Bit c::s=>if Eqb.eqb b c then literal_strip bs s else None
    | _=>None end end.
Lemma literal_strip_spec bs s t d : literal_strip bs s=Some t ->
  denote d s=bs *> denote d t.
Proof.
  revert s; induction bs as [|b bs IH]; intros s H; [injection H as <-; reflexivity|].
  destruct s as [|[c|p x z|cs|n]s]; try discriminate.
  destruct b,c; cbn[literal_strip]in H; try discriminate;
    rewrite denote_bit,(IH _ H); reflexivity.
Qed.
Definition take_left k := match k with V2FP=>strip | _=>fun bs d s=>literal_strip bs s end.
Lemma take_left_spec k bs d s t : take_left k bs d s=Some t ->
  denote d s=bs *> denote d t.
Proof. destruct k; try apply literal_strip_spec; apply strip_spec. Qed.
Definition run_kernel k l r := let p:=description k in
  match literal_strip(ir p)r with None=>None | Some r'=>
  match take_left k(il p)L l with None=>None | Some l'=>
    Some(Cfg(oq p)(od p)(prepend(ol p)l')(prepend(orr p)r')) end end.
Lemma run_kernel_spec k l r c : run_kernel k l r=Some c ->
  decode(Cfg(iq(description k))(id(description k))l r) -[tm]->* decode c.
Proof.
  unfold run_kernel; destruct(literal_strip(ir(description k))r)as [r'|]eqn:Rr; [|discriminate].
  destruct(take_left k(il(description k))L l)as [l'|]eqn:Ll; [|discriminate].
  intro H; injection H as <-.
  pose proof(@literal_strip_spec _ _ _ R Rr)as HR.
  pose proof(@take_left_spec _ _ _ _ _ Ll)as HL.
  change(plain(iq(description k))(id(description k))(denote L l)(denote R r)
    -[tm]->* plain(oq(description k))(od(description k))
       (denote L(prepend(ol(description k))l'))(denote R(prepend(orr(description k))r'))).
  rewrite !prepend_spec,HL,HR; apply kernel_spec.
Qed.

(* A short W-band may be a newly made endpoint.  Never unfold a long band
   for speculative actor matching.  The right view only exposes one column. *)
Definition right_view s := match s with Band p x z::s'=>
  match SharedDeck.front z,SharedDeck.back z with
  | [a],[] | [],[a]=>prepend(dword R p x a)s' | _,_=>s end | _=>s end.
Lemma right_view_spec s : denote R(right_view s)=denote R s.
Proof.
  destruct s as [|[b|p x [f g k]|bs|n]s]; try reflexivity.
  destruct f as [|a [|b f]],g as [|c [|d g]]; try reflexivity;
    cbn[right_view SharedDeck.front SharedDeck.back];
    rewrite prepend_spec,denote_band; unfold bits; cbn[SharedDeck.contents SharedDeck.front SharedDeck.back rev flat_map app];
    rewrite app_nil_r; reflexivity.
Qed.
Definition literal_zero s := match s with Bit 0::_=>true | _=>false end.
Definition right_actor l r := if literal_zero r then
  match run_kernel Q4Enter l r with Some c=>Some c | None=>
  match run_kernel Q3Enter l r with Some c=>Some c | None=>
  match run_kernel Q2Reflect l r with Some c=>Some c | None=>
  run_kernel StarReflect l r end end end else None.
Definition e_actor l r := if literal_zero l then
  match run_kernel Q4Second l r with Some c=>Some c | None=>
  match run_kernel Q4Return l r with Some c=>Some c | None=>
  run_kernel Q3E l r end end else None.
Definition f_actor l r :=
  match (if literal_zero l then run_kernel Q3F l r else None) with
  | Some c=>Some c | None=>run_kernel V2FP l r end.
Definition actor_core c := match c with
  | Cfg C R l r=>right_actor l(right_view r)
  | Cfg E L l r=>e_actor l r
  | Cfg D L l r=>if literal_zero l then run_kernel Q3D l r else None
  | Cfg F L l r=>f_actor l r | _=>None end.
(* Specialize the ten closed packets and their constant reversals/projections.
   The bounded recognizers remain shared: fully expanding them bloats extraction. *)
Definition actor := Eval cbv[actor_core right_actor e_actor f_actor run_kernel description
  take_left iq id il ir oq od ol orr
  Q4 Z4 Z4' W V bridge_in bridge_out bridge_back bridge_back_F rev app]in actor_core.
Ltac kernel_cases :=
  repeat match goal with
  | |- context[if ?b then _ else _]=>destruct b eqn:?; try discriminate
  | |- context[match run_kernel ?k ?l ?r with Some _=>_ | None=>_ end]=>
      let E:=fresh "K" in let T:=fresh "T" in
      destruct(run_kernel k l r)eqn:E;
        [intro T; injection T as <-; exact(@run_kernel_spec k l r _ E)|]
  end;
  match goal with |- run_kernel ?k ?l ?r=Some ?c -> _ => exact(@run_kernel_spec k l r c) end.
Lemma right_actor_spec l r c : right_actor l r=Some c ->
  decode(Cfg C R l r) -[tm]->* decode c.
Proof. unfold right_actor; kernel_cases. Qed.
Lemma e_actor_spec l r c : e_actor l r=Some c ->
  decode(Cfg E L l r) -[tm]->* decode c.
Proof. unfold e_actor; kernel_cases. Qed.
Lemma f_actor_spec l r c : f_actor l r=Some c ->
  decode(Cfg F L l r) -[tm]->* decode c.
Proof. unfold f_actor; kernel_cases. Qed.
Lemma actor_spec c c' : actor c=Some c' -> decode c -[tm]->* decode c'.
Proof.
  change(actor_core c=Some c' -> decode c -[tm]->* decode c').
  destruct c as [q d l r]; destruct q,d; cbn[actor_core]; try discriminate.
  - intro H; pose proof(@right_actor_spec _ _ _ H)as K.
    cbn[decode DirectedChecker.decode]in K |- *; rewrite right_view_spec in K; exact K.
  - destruct(literal_zero l); [apply run_kernel_spec|discriminate].
  - apply e_actor_spec.
  - apply f_actor_spec.
Qed.
Definition macro c := match actor c with Some c'=>Some c' | None=>Checker.macro c end.
Lemma macro_spec c c' : macro c=Some c' -> decode c -[tm]->* decode c'.
Proof. unfold macro; destruct(actor c)eqn:E; [intro H; injection H as <-; apply actor_spec,E|apply Checker.macro_spec]. Qed.
End Actors.

Module Higher1.
Definition edge (b:bool) := if b then Zero else Star.
Definition qend (b:bool) : list Sym :=
  if b then [0;1;1;1;1;1;1] else [0;1;1;1;1].
Definition dword1 : list Sym := [1;1;0;0;0].
Definition block : list Sym := [0;0;0;1;1].
Definition tail0 : list Sym := [1;1;0;0;0;1;1].

Lemma d_one l t : l <* rev(V One) <{{D}} t -[tm]->*
  l <{{D}} dword1 *> t.
Proof. unfold V,dword1; esx. Qed.
Lemma d_edge b l t : l <* rev(V(edge b)) <{{D}} t -[tm]->*
  l <{{E}} W(swap(edge b)) *> t.
Proof. destruct b; unfold edge,V,W,swap; esx. Qed.

Lemma ones_return r l t :
  l {{C}}> (Ws(repeat One r)++W One++[0;0]) *> t -[tm]->*
  l <{{D}} (dword1^^r++tail0) *> t.
Proof.
  revert l; induction r as [|r IH]; intro l.
  - cbn[repeat Ws flat_map lpow app]; apply progress_evstep,q2_return.
  - cbn[repeat Ws flat_map lpow]; rewrite !Str_app_assoc.
    rewrite !Str_app_assoc in IH.
    eapply evstep_trans; [apply forward_word|].
    eapply evstep_trans; [apply IH|apply d_one].
Qed.

Lemma payload r : dword1^^r++tail0=[1;1]++block^^(S r).
Proof.
  induction r as [|r IH]; [reflexivity|].
  cbn[lpow]; rewrite <-app_assoc,IH; reflexivity.
Qed.
Lemma endpoint_payload b r :
  W(swap(edge b))++dword1^^r++tail0=qend b++block^^(S r).
Proof. rewrite payload; destruct b; reflexivity. Qed.

Lemma endpoint_return b r l t :
  l {{C}}> (W(edge b)++Ws(repeat One r)++W One++[0;0]) *> t -[tm]->*
  l <{{E}} (qend b++block^^(S r)) *> t.
Proof.
  rewrite <-endpoint_payload,!Str_app_assoc.
  eapply evstep_trans; [apply forward_word|].
  pose proof(@ones_return r(rev(V(edge b)) *> l)t)as H.
  rewrite !Str_app_assoc in H.
  eapply evstep_trans; [exact H|apply d_edge].
Qed.

Lemma one_return xs b r l t :
  l {{C}}> (Ws(xs++edge b::repeat One r)++W One++[0;0]) *> t -[tm]->*
  l <{{E}} (Ws(swaps xs)++qend b++block^^(S r)) *> t.
Proof.
  unfold Ws; rewrite !flat_map_app; cbn[flat_map].
  rewrite !Str_app_assoc.
  eapply evstep_trans; [apply forward_words|].
  pose proof(@endpoint_return b r(rev(Vs xs) *> l)t)as H.
  rewrite !Str_app_assoc in H.
  eapply evstep_trans; [exact H|apply backward_words].
Qed.

Lemma one_count bs bs' xs b r l t : increment bs=Some bs' ->
  l <* left_digits bs {{C}}> (Ws(xs++edge b::repeat One r)++W One++[0;0]) *> t -[tm]->*
  l <* left_digits bs' {{C}}> (Ws(swaps xs)++qend b++block^^(S r)) *> t.
Proof.
  intro H; eapply evstep_trans; [apply one_return|apply increment_spec,H].
Qed.

Import Checker.
(* Search only the consumed suffix.  A front reversal is done only after the
   back is exhausted; a successful result retains that orientation for reuse.
   There is no conversion of a whole-band length to unary fuel. *)
Inductive suffix := Pure (n:nat) | Hit (b:bool)(n:nat)(rest:list letter).
Fixpoint scan x cs := match cs with
  | []=>Pure 0
  | a::cs=>match actual x a with
    | Star=>Hit false 0 cs | Zero=>Hit true 0 cs
    | One=>match scan x cs with Pure n=>Pure(S n)
      | Hit b n rest=>Hit b(S n)rest end end end.
Lemma scan_spec x cs : match scan x cs with
  | Pure n=>map(actual x)cs=repeat One n
  | Hit b n rest=>map(actual x)cs=repeat One n++edge b::map(actual x)rest end.
Proof.
  induction cs as [|a cs IH]; [reflexivity|].
  cbn[scan]; destruct(actual x a)eqn:E; cbn[map]; rewrite E;
    try reflexivity.
  destruct(scan x cs); cbn in IH |- *; rewrite IH; reflexivity.
Qed.
Record answer := Answer { choice:bool; run:nat; prefix:deck }.
Definition tail_split x z := match scan x(SharedDeck.back z) with
  | Hit b r rest=>Some(Answer b r(SharedDeck.Deck(SharedDeck.front z)rest
      (N.sub(SharedDeck.weight z)(N.of_nat(S r)))))
  | Pure k=>match scan x(fast_rev(SharedDeck.front z))with
    | Pure _=>None
    | Hit b r rest=>Some(Answer b(r+k)(SharedDeck.Deck [] rest
      (N.sub(SharedDeck.weight z)(N.of_nat(S(r+k)))))) end end.
Lemma tail_split_spec x z a : tail_split x z=Some a ->
  map(actual x)(SharedDeck.contents z)=
  map(actual x)(SharedDeck.contents(prefix a))++edge(choice a)::repeat One(run a).
Proof.
  destruct z as [f g w]; unfold tail_split; cbn[SharedDeck.front SharedDeck.back SharedDeck.weight].
  pose proof(scan_spec x g)as G; destruct(scan x g)as [k|b r rest]eqn:EG.
  - pose proof(scan_spec x(fast_rev f))as F.
    destruct(scan x(fast_rev f))as [j|b r rest]eqn:EF; [discriminate|].
    intro H; injection H as <-; cbn[prefix choice run].
    rewrite fast_rev_spec,map_rev in F.
    pose proof(f_equal (@rev letter) F)as RF; rewrite rev_involutive in RF.
    unfold SharedDeck.contents; cbn[SharedDeck.front SharedDeck.back].
    rewrite !map_app,!map_rev,G,rev_repeat,RF,rev_app_distr,rev_repeat.
    cbn[rev app map]; rewrite repeat_app; rewrite <-?app_assoc; reflexivity.
  - intro H; injection H as <-; cbn[prefix choice run].
    unfold SharedDeck.contents; cbn[SharedDeck.front SharedDeck.back].
    rewrite !map_app,!map_rev,G,rev_app_distr,rev_repeat.
    cbn[rev]; rewrite <-?app_assoc; reflexivity.
Qed.

Definition finish l r := match l with Count bs::l'=>
  match increment bs with Some cs=>DirectedChecker.Cfg C R(put_count cs l')r
  | None=>DirectedChecker.Cfg E L l r end
  | _=>DirectedChecker.Cfg E L l r end.
Lemma finish_spec l r : decode(DirectedChecker.Cfg E L l r) -[tm]->* decode(finish l r).
Proof.
  unfold finish; destruct l as [|[b|p x z|bs|n]l]; try apply evstep_refl.
  destruct(increment bs)as [cs|]eqn:H; [|apply evstep_refl].
  cbn[decode DirectedChecker.decode]; rewrite denote_count,put_count_spec.
  apply increment_spec,H.
Qed.
Definition one c := match c with
  | DirectedChecker.Cfg C R l(Band false x z::r)=>
    match Actors.literal_strip(W One++[0;0])r with None=>None | Some t=>
    match tail_split x z with None=>None | Some a=>
      Some(finish l(put_band false(negb x)(prefix a)
        (prepend(qend(choice a)++block^^(S(run a)))t))) end end
  | _=>None end.
Lemma one_spec c c' : one c=Some c' -> decode c -[tm]->* decode c'.
Proof.
  destruct c as [q d l r]; destruct q,d; cbn[one]; try discriminate.
  destruct r as [|[v|p x z|bs|n]r]; try discriminate.
  destruct p; [discriminate|].
  destruct(Actors.literal_strip(W One++[0;0])r)as [t|]eqn:T; [|discriminate].
  destruct(tail_split x z)as [a|]eqn:S; [|discriminate].
  intro H; injection H as <-.
  eapply evstep_trans; [|apply finish_spec].
  cbn[decode DirectedChecker.decode].
  rewrite denote_band,bits_R_W,(@tail_split_spec x z a S).
  rewrite(@Actors.literal_strip_spec (W One++[0;0])r t R T).
  rewrite put_band_spec,prepend_spec,bits_R_W,actual_swaps.
  pose proof(@one_return(map(actual x)(SharedDeck.contents(prefix a)))
    (choice a)(run a)(denote L l)(denote R t))as K.
  rewrite <-!Str_app_assoc; exact K.
Qed.
End Higher1.

Module Higher2.
Import Higher1.

Lemma d_ones r l t : l <* rev(Vs(repeat One r)) <{{D}} t -[tm]->*
  l <{{D}} dword1^^r *> t.
Proof.
  revert l t; induction r as [|r IH]; intros l t; [apply evstep_refl|].
  cbn[repeat Vs flat_map lpow]; rewrite rev_app_distr,!Str_app_assoc.
  eapply evstep_trans; [apply IH|apply d_one].
Qed.

Lemma star_zero l t : l <* [0;0;0;1] <{{E}} t -[tm]->*
  l <{{D}} [1;1;0;0] *> t.
Proof. esx. Qed.

Lemma left_payload r : dword1^^r++[1;1;0;0]=[1;1]++block^^r++[0;0].
Proof.
  induction r as [|r IH]; [reflexivity|].
  cbn[lpow]; rewrite <-app_assoc,IH; reflexivity.
Qed.
Lemma edge_payload b r :
  W(swap(edge b))++dword1^^r++[1;1;0;0]=qend b++block^^r++[0;0].
Proof. rewrite left_payload; destruct b; reflexivity. Qed.

Lemma left_return xs b r l t :
  l <* rev(Vs(xs++edge b::repeat One r)++V Star++[0]) <{{E}} t -[tm]->*
  l <{{E}} (Ws(swaps xs)++qend b++block^^r++[0;0]) *> t.
Proof.
  rewrite <-edge_payload.
  unfold Vs; rewrite !flat_map_app; cbn[flat_map].
  rewrite !rev_app_distr,!Str_app_assoc.
  eapply evstep_trans; [apply star_zero|].
  eapply evstep_trans; [apply d_ones|].
  eapply evstep_trans; [apply d_edge|apply backward_words].
Qed.

Lemma reflect_star xs l t :
  l {{C}}> (Ws xs++W Star++[0;0]) *> t -[tm]->*
  l <{{E}} (Ws(swaps xs)++W One) *> t.
Proof.
  rewrite !Str_app_assoc.
  eapply evstep_trans; [apply forward_words|].
  eapply evstep_trans; [apply progress_evstep,star_return|apply backward_words].
Qed.
Definition middle k := Zero::One::Star::(repeat Star k++[One]).
Lemma bridge k l t :
  l {{C}}> (W One++bridge_in++Ws(repeat Star k)++W Star++[0;0]) *> t -[tm]->*
  l <* rev([0]++Vs(middle k)) {{C}}> t.
Proof.
  rewrite !Str_app_assoc.
  eapply evstep_trans; [apply forward_word|].
  eapply evstep_trans; [apply bridge_forward|].
  pose proof(@reflect_star(repeat Star k)
    (rev bridge_out *> rev(V One) *> l)t)as H.
  unfold swaps in H; rewrite map_repeat in H; cbn[swap]in H.
  rewrite !Str_app_assoc in H.
  eapply evstep_trans; [exact H|].
  eapply evstep_trans; [apply bridge_return|].
  eapply evstep_trans; [apply bridge_restart|].
  unfold Vs,middle; cbn[flat_map]; rewrite flat_map_app.
  cbn[flat_map]; rewrite app_nil_r,!rev_app_distr,!Str_app_assoc.
  eapply evstep_trans; [apply forward_words|apply forward_word].
Qed.

Lemma suffix_return xs b r k l t :
  l <* rev(Vs(xs++edge b::repeat One r)++V Star++[0]++Vs(middle k)) <{{E}} t -[tm]->*
  l <{{E}} (Ws(swaps xs)++qend b++block^^r++[0;0]++Ws(swaps(middle k))) *> t.
Proof.
  rewrite !rev_app_distr,!Str_app_assoc.
  eapply evstep_trans; [apply backward_words|].
  pose proof(@left_return xs b r l(Ws(swaps(middle k)) *> t))as H.
  rewrite !rev_app_distr,!Str_app_assoc in H; exact H.
Qed.

Lemma two_return xs b r ys c s k l t :
  l {{C}}> (Ws(xs++edge b::repeat One r)++W Star++W One++bridge_in++
    Ws(repeat Star k)++W Star++[0;0]++
    Ws(ys++edge c::repeat One s)++W One++[0;0]) *> t -[tm]->*
  l <{{E}} (Ws(swaps xs)++qend b++block^^r++[0;0]++Ws(swaps(middle k))++
    Ws(swaps ys)++qend c++block^^(S s)) *> t.
Proof.
  rewrite !Str_app_assoc.
  eapply evstep_trans; [apply forward_words|].
  eapply evstep_trans; [apply forward_word|].
  pose proof(@bridge k(rev(V Star) *> rev(Vs(xs++edge b::repeat One r)) *> l)
    ((Ws(ys++edge c::repeat One s)++W One++[0;0]) *> t))as B.
  rewrite !Str_app_assoc in B.
  eapply evstep_trans; [exact B|].
  pose proof(@one_return ys c s
    (rev([0]++Vs(middle k)) *> rev(V Star) *>
      rev(Vs(xs++edge b::repeat One r)) *> l)t)as H.
  rewrite !Str_app_assoc in H.
  eapply evstep_trans; [exact H|].
  pose proof(@suffix_return xs b r k l
    ((Ws(swaps ys)++qend c++block^^(S s)) *> t))as K.
  repeat rewrite rev_app_distr in K.
  repeat rewrite Str_app_assoc in K.
  rewrite !rev_app_distr,!Str_app_assoc; exact K.
Qed.

Import Checker.
Definition pop_last (z:deck) := match SharedDeck.pop(SharedDeck.flip z)with
  | None=>None | Some(a,w)=>Some(a,SharedDeck.flip w)end.
Lemma pop_last_spec z a w : pop_last z=Some(a,w) ->
  SharedDeck.contents z=SharedDeck.contents w++[a].
Proof.
  unfold pop_last; pose proof(SharedDeck.pop_spec(SharedDeck.flip z))as P.
  destruct(SharedDeck.pop(SharedDeck.flip z))as [[b v]|]eqn:E; [|discriminate].
  intro H; injection H as <- <-.
  rewrite SharedDeck.flip_spec in P; cbn in P.
  apply(f_equal(@rev letter))in P; rewrite rev_involutive in P.
  rewrite SharedDeck.flip_spec; exact P.
Qed.
(* At most two labels are inspected before scanning the consumed One suffix.
   The underlying balanced pop only rebuilds an empty deque side. *)
Definition tail_pair x z := match pop_last z with None=>None | Some(a,w)=>
  match actual x a with One=>match pop_last w with None=>None | Some(b,v)=>
    match actual x b with Star=>Some v | _=>None end end | _=>None end end.
Lemma tail_pair_spec x z w : tail_pair x z=Some w ->
  map(actual x)(SharedDeck.contents z)=map(actual x)(SharedDeck.contents w)++[Star;One].
Proof.
  unfold tail_pair; destruct(pop_last z)as [[a u]|]eqn:A; [|discriminate].
  destruct(actual x a)eqn:EA; try discriminate.
  destruct(pop_last u)as [[b v]|]eqn:B; [|discriminate].
  destruct(actual x b)eqn:EB; try discriminate.
  intro H; injection H as <-.
  rewrite(@pop_last_spec z a u A),(@pop_last_spec u b v B),!map_app.
  cbn[map]; rewrite EA,EB,<-app_assoc; reflexivity.
Qed.

Fixpoint stars_tail (fuel:nat)(s:list token) : option(nat*list token) :=
  match Actors.literal_strip [0;0]s with Some t=>Some(O,t) | None=>
  match fuel with O=>None | S k=>
    match Actors.literal_strip(W Star)s with None=>None | Some u=>
      match stars_tail k u with None=>None | Some(n,t)=>Some(S n,t)end end end end.
Lemma stars_tail_spec fuel s n t : stars_tail fuel s=Some(n,t) ->
  denote R s=(Ws(repeat Star n)++[0;0]) *> denote R t.
Proof.
  revert s n t; induction fuel as [|k IH]; intros s n t;
    cbn[stars_tail]; destruct(Actors.literal_strip [0;0]s)as [u|]eqn:E.
  - intro H; injection H as <- <-; exact(@Actors.literal_strip_spec [0;0]s u R E).
  - discriminate.
  - intro H; injection H as <- <-; exact(@Actors.literal_strip_spec [0;0]s u R E).
  - destruct(Actors.literal_strip(W Star)s)as [u|]eqn:W; [|discriminate].
    destruct(stars_tail k u)as [[j v]|]eqn:T; [|discriminate].
    intro H; injection H as <- <-.
    rewrite(@Actors.literal_strip_spec (TM28.W Star)s u R W),(IH _ _ _ T).
    cbn[repeat Ws flat_map]; rewrite <-!Str_app_assoc; reflexivity.
Qed.

Lemma stars_snoc k : Ws(repeat Star(S k))=Ws(repeat Star k)++W Star.
Proof.
  induction k as [|k IH]; [reflexivity|].
  cbn[repeat Ws flat_map]in IH |- *; rewrite <-app_assoc,IH; reflexivity.
Qed.
Lemma primary_spec x z w a : tail_pair x z=Some w -> tail_split x w=Some a ->
  bits R false x z=
  Ws(map(actual x)(SharedDeck.contents(prefix a))++edge(choice a)::repeat One(run a))++W Star++W One.
Proof.
  intros P S; rewrite bits_R_W,(@tail_pair_spec x z w P),(@tail_split_spec x w a S).
  unfold Ws; rewrite flat_map_app; cbn[flat_map]; rewrite app_nil_r; reflexivity.
Qed.
Definition middle_deck k := SharedDeck.Deck(middle k)[](N.of_nat(k+4)).
Lemma middle_bits k : bits R false true(middle_deck k)=Ws(swaps(middle k)).
Proof.
  rewrite bits_R_W; unfold middle_deck,SharedDeck.contents.
  cbn[SharedDeck.front SharedDeck.back rev]; rewrite app_nil_r; reflexivity.
Qed.
Definition emit x a y b k t :=
  put_band false(negb x)(prefix a)
    (prepend(qend(choice a)++block^^run a++[0;0])
      (put_band false true(middle_deck k)
        (put_band false(negb y)(prefix b)
          (prepend(qend(choice b)++block^^S(run b))t)))).
Lemma emit_spec x a y b k t : denote R(emit x a y b k t)=
  (Ws(swaps(map(actual x)(SharedDeck.contents(prefix a))))++
    qend(choice a)++block^^run a++[0;0]++Ws(swaps(middle k))++
    Ws(swaps(map(actual y)(SharedDeck.contents(prefix b))))++
    qend(choice b)++block^^S(run b)) *> denote R t.
Proof.
  unfold emit; repeat first [rewrite put_band_spec|rewrite prepend_spec].
  rewrite middle_bits,!bits_R_W,!actual_swaps.
  repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc; reflexivity.
Qed.
Definition two c := match c with
  | DirectedChecker.Cfg C R l(Band false x z::r)=>
    match Actors.literal_strip bridge_in r with None=>None | Some u=>
    match stars_tail 64 u with Some(S k,Band false y w::v)=>
    match Actors.literal_strip(W One++[0;0])v with None=>None | Some t=>
    match tail_pair x z with None=>None | Some z'=>
    match tail_split x z' with None=>None | Some a=>
    match tail_split y w with None=>None | Some b=>
      Some(finish l(emit x a y b k t))end end end end
    | _=>None end end
  | _=>None end.

Lemma two_spec c c' : two c=Some c' -> decode c -[tm]->* decode c'.
Proof.
  destruct c as [q d l r]; destruct q,d; cbn[two]; try discriminate.
  destruct r as [|[v|p x z|bs|n]r]; try discriminate.
  destruct p; [discriminate|].
  destruct(Actors.literal_strip bridge_in r)as [u|]eqn:B; [|discriminate].
  destruct(stars_tail 64 u)as [[m s2]|]eqn:ST; [|discriminate].
  destruct m as [|k]; [discriminate|].
  destruct s2 as [|[v|p y w|bs|n]v2]; try discriminate.
  destruct p; [discriminate|].
  destruct(Actors.literal_strip(W One++[0;0])v2)as [t|]eqn:T; [|discriminate].
  destruct(tail_pair x z)as [z'|]eqn:P; [|discriminate].
  destruct(tail_split x z')as [a|]eqn:SX; [|discriminate].
  destruct(tail_split y w)as [b|]eqn:U; [|discriminate].
  intro H; injection H as <-.
  eapply evstep_trans; [|apply finish_spec].
  cbn[decode DirectedChecker.decode].
  rewrite denote_band,(@primary_spec x z z' a P SX).
  rewrite(@Actors.literal_strip_spec bridge_in r u R B).
  rewrite(@stars_tail_spec 64 u(S k)(Band false y w::v2)ST),stars_snoc.
  rewrite denote_band,bits_R_W,(@tail_split_spec y w b U).
  rewrite(@Actors.literal_strip_spec (W One++[0;0])v2 t R T),emit_spec.
  pose proof(@two_return(map(actual x)(SharedDeck.contents(prefix a)))
    (choice a)(run a)(map(actual y)(SharedDeck.contents(prefix b)))
    (choice b)(run b)k(denote L l)(denote R t))as K.
  repeat rewrite Str_app_assoc in K.
  repeat rewrite Str_app_assoc; exact K.
Qed.
Definition macro c := match Higher1.one c with Some c'=>Some c' | None=>
  match two c with Some c'=>Some c' | None=>Actors.macro c end end.
Lemma macro_spec c c' : macro c=Some c' -> decode c -[tm]->* decode c'.
Proof.
  unfold macro; destruct(Higher1.one c)eqn:E.
  - intro H; injection H as <-; apply Higher1.one_spec,E.
  - destruct(two c)eqn:T.
    + intro H; injection H as <-; apply two_spec,T.
    + apply Actors.macro_spec.
Qed.
Definition iterate := Eval cbv[DirectedChecker.iterate DirectedChecker.iterate_pos
  DirectedChecker.chain DirectedChecker.advance DirectedChecker.raw]in
  @DirectedChecker.iterate token tm pop push macro.
Definition check n q := match iterate n(DirectedChecker.Cfg q R [] [])with
  None=>true | _=>false end.
Lemma check_spec n q : check n q=true -> halts tm(0inf {{q}}> 0inf).
Proof.
  apply(@DirectedChecker.check_spec token tm denote pop push
    denote_empty pop_spec push_spec macro macro_spec).
Qed.

End Higher2.

Theorem halt: halts tm c0.
Proof. apply(@Higher2.check_spec 5000000000%N A). native_check_eq. Time Qed.
End TM28.

Module TM27.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RC").
Definition state_map q := match q with A=>C | B=>A | C=>B | D=>D | E=>E | F=>F end.
Lemma same_table : Perm tm TM28.tm state_map.
Proof.
  split.
  - intros q b; destruct q,b; cbn; congruence.
  - intros q b w d q' H; destruct q,b; cbn in H; try discriminate;
      inversion H; subst; reflexivity.
Qed.
Lemma from_check n : TM28.Higher2.check n C=true -> halts tm c0.
Proof.
  intro H; apply(@perm_halts' tm TM28.tm state_map A (0inf {{S0}} 0inf) same_table).
  apply(@TM28.Higher2.check_spec n C),H.
Qed.
Theorem halt: halts tm c0.
Proof. apply(@from_check 40000000000%N). native_check_eq. Time Qed.
End TM27.

Print Assumptions TM28.halt.
Print Assumptions TM27.halt.
