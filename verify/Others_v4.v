(* Fifth Others machine: specialized binary counters and recursively typed
   invariant words.  The final computation starts from the blank configuration;
   no checkpoints, cached windows, or external trace data enter this proof. *)
From BusyCoq Require Import Individual62 Longitudinal ES_v3 FastRev.
Require Import ZifyNat Lia String List PeanoNat NArith.
Set Implicit Arguments.

Module TM.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC0RB_0LA1RE_1LA0LB_0RA0RF_---0LC").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Definition W (b:bool) : list Sym := if b then [0;1;1;1] else [0;1;0;0].
Definition V (b:bool) : list Sym := if b then [0;1;1;0] else [1;1;1;0].
Definition Ws := flat_map W.
Definition Vs := flat_map V.
Notation hH := (B,[1]).
Notation hN := (D,[1]).

Lemma H_word b: segRR tm hH hH (W b) (rev(V b)).
Proof. destruct b; unfold segRR,W,V; intros; esx. Qed.
Lemma G_word b l r:
  (l <* rev(V b)) << 1 <{{A}} r -->* l << 1 <{{A}} W b *> r.
Proof. destruct b; unfold W,V; esx. Qed.
Lemma N_word b: segLL tm hN hN (rev(V b)) (W b).
Proof. destruct b; unfold segLL,W,V; intros; esx. Qed.
Lemma H_reflect l r:
  l << 1 {{B}}> [0;1;0;1] *> r -->+ l << 1 <{{A}} [0;1;0;0] *> r.
Proof. esx. Qed.

Lemma H_words bs: segRR tm hH hH (Ws bs) (rev(Vs bs)).
Proof.
  induction bs as [|b bs IH]; [intros l r; apply evstep_refl|].
  unfold segRR in *; intros l r; cbn[Ws Vs flat_map].
  rewrite rev_app_distr,!Str_app_assoc.
  unfold to_DH_config in *.
  eapply evstep_trans; [apply H_word|apply IH].
Qed.
Lemma G_words bs l r:
  (l <* rev(Vs bs)) << 1 <{{A}} r -->* l << 1 <{{A}} Ws bs *> r.
Proof.
  revert l r; induction bs as [|b bs IH]; intros l r.
  - apply evstep_refl.
  - cbn[Ws Vs flat_map]; rewrite rev_app_distr,!Str_app_assoc.
    eapply evstep_trans; [apply IH|apply G_word].
Qed.
Lemma N_words bs: segLL tm hN hN (rev(Vs bs)) (Ws bs).
Proof.
  induction bs as [|b bs IH]; [intros l r; apply evstep_refl|].
  unfold segLL in *; intros l r; cbn[Ws Vs flat_map].
  rewrite rev_app_distr,!Str_app_assoc.
  unfold to_DH_config in *.
  eapply evstep_trans; [apply IH|apply N_word].
Qed.
Lemma HG_words bs l r:
  l << 1 {{B}}> Ws bs *> [0;1;0;1] *> r -->+
  l << 1 <{{A}} Ws bs *> [0;1;0;0] *> r.
Proof.
  eapply evstep_progress_trans; [apply H_words|].
  eapply progress_evstep_trans; [apply H_reflect|apply G_words].
Qed.

(* Bare-head reversible passages.  Unlike W, a strong passage does not need
   the neighboring 1 payload.  This stronger interface closes the recursive
   grammar found in the actual right counter separators. *)
Definition strong (s t:list Sym) :=
  segRR tm (B,[]) (B,[]) s (rev t) /\
  segLL tm (A,[]) (A,[]) (rev t) s.
Definition weak (s t:list Sym) :=
  segRR tm hH hH s (rev t) /\
  forall l r, (l <* rev t) << 1 <{{A}} r -->* l << 1 <{{A}} s *> r.

Lemma strong_empty: strong [] [].
Proof. split; intros l r; apply evstep_refl. Qed.
Lemma weak_empty: weak [] [].
Proof. split; intros l r; apply evstep_refl. Qed.
Lemma weak_W b: weak (W b) (V b).
Proof. split; [apply H_word|apply G_word]. Qed.

Definition box_in b s : list Sym := [1;1]++s++[1;1;0;1;b;b].
Definition box_out b t : list Sym := [0;b]++t++[0;0;1;1;0;1].

Lemma box_strong b s t: strong s t -> strong (box_in b s) (box_out b t).
Proof.
  intros [F G]; split; unfold segRR,segLL in *; intros l r;
    unfold box_in,box_out; rewrite !rev_app_distr; cbn[rev];
    rewrite !Str_app_assoc; unfold to_DH_config in *; cbn[Str_app].
  - destruct b.
    + steps; follow F; esx.
    + steps; follow F; steps; follow G; steps; follow F; esx.
  - destruct b.
    + steps; follow G; steps; follow F; steps; follow G; esx.
    + steps; follow G; esx.
Qed.

Lemma weak_app s1 t1 s2 t2:
  weak s1 t1 -> weak s2 t2 -> weak (s1++s2) (t1++t2).
Proof.
  intros [F1 G1] [F2 G2]; split.
  - unfold segRR in *; intros l r; rewrite rev_app_distr,!Str_app_assoc.
    unfold to_DH_config in *.
    eapply evstep_trans; [apply F1|apply F2].
  - intros l r; rewrite rev_app_distr,!Str_app_assoc.
    eapply evstep_trans; [apply G2|apply G1].
Qed.

Lemma strong_weak_append s t w v:
  strong s (t++[1]) -> weak w v -> strong (s++w) (t++v++[1]).
Proof.
  intros [F G] [FW GW]; split; unfold segRR,segLL in *; intros l r;
    rewrite !rev_app_distr; cbn[rev]; rewrite !Str_app_assoc;
    unfold to_DH_config in *; cbn[Str_app].
  - eapply evstep_trans; [apply F|].
    rewrite rev_app_distr; cbn[rev Str_app]; apply FW.
  - eapply evstep_trans; [apply GW|].
    specialize (G l (w *> r)); rewrite rev_app_distr in G; exact G.
Qed.

Lemma strong_weak s t: strong s (t++[1]) -> weak s ([1]++t).
Proof.
  intros [F G]; split; unfold segRR,segLL in *; intros l r;
    rewrite !rev_app_distr; cbn[rev]; rewrite !Str_app_assoc;
    unfold to_DH_config in *; cbn[Str_app].
  - specialize (F (l << 1) r); rewrite rev_app_distr in F.
    cbn[rev Str_app] in F; repeat rewrite Str_app_assoc; exact F.
  - specialize (G (l << 1) r); rewrite rev_app_distr in G.
    cbn[rev Str_app] in G; repeat rewrite Str_app_assoc; exact G.
Qed.

Definition box_prefix b t : list Sym := [0;b]++t++[0;0;1;1;0].
Lemma box_out_last b t: box_out b t=box_prefix b t++[1].
Proof. unfold box_out,box_prefix; rewrite <-!app_assoc; reflexivity. Qed.
Lemma box_weak b s t: strong s t -> weak (box_in b s) ([1]++box_prefix b t).
Proof.
  intro H; apply strong_weak; rewrite <-box_out_last; apply box_strong,H.
Qed.

(* Strong bodies are empty, or start with a framed passage.  Their remaining
   suffix may contain either W letters or more frames.  This typed grammar
   deliberately does NOT allow an arbitrary W-leading body. *)
Inductive sequence : Type :=
| SEmpty
| SFrame (b:Sym) (body:sequence) (suffix:tail)
with tail : Type :=
| TEmpty
| TWord (b:bool) (suffix:tail)
| TFrame (b:Sym) (body:sequence) (suffix:tail).

Fixpoint sequence_in s : list Sym := match s with
  | SEmpty=>[]
  | SFrame b body suffix=>box_in b (sequence_in body)++tail_in suffix end
with tail_in s : list Sym := match s with
  | TEmpty=>[]
  | TWord b suffix=>W b++tail_in suffix
  | TFrame b body suffix=>box_in b (sequence_in body)++tail_in suffix end.
Fixpoint sequence_out s : list Sym := match s with
  | SEmpty=>[]
  | SFrame b body suffix=>box_prefix b (sequence_out body)++tail_out suffix++[1] end
with tail_out s : list Sym := match s with
  | TEmpty=>[]
  | TWord b suffix=>V b++tail_out suffix
  | TFrame b body suffix=>([1]++box_prefix b (sequence_out body))++tail_out suffix end.

Scheme sequence_ind' := Induction for sequence Sort Prop
with tail_ind' := Induction for tail Sort Prop.
Combined Scheme grammar_ind from sequence_ind',tail_ind'.

Lemma grammar_sound:
  (forall s, strong (sequence_in s) (sequence_out s)) /\
  (forall t, weak (tail_in t) (tail_out t)).
Proof.
  apply grammar_ind; cbn[sequence_in sequence_out tail_in tail_out].
  - apply strong_empty.
  - intros b body HB suffix HS; apply strong_weak_append; [|exact HS].
    rewrite <-box_out_last; apply box_strong,HB.
  - apply weak_empty.
  - intros b suffix HS; apply weak_app; [apply weak_W|exact HS].
  - intros b body HB suffix HS; apply weak_app; [apply box_weak,HB|exact HS].
Qed.
Lemma sequence_sound s: strong (sequence_in s) (sequence_out s).
Proof. apply grammar_sound. Qed.
Lemma tail_sound s: weak (tail_in s) (tail_out s).
Proof. apply grammar_sound. Qed.

Lemma successor_path a b a' b':
  a -->* b -> a -[tm]-> a' -> b -[tm]-> b' -> a' -->* b'.
Proof.
  intros H Ha Hb; destruct H as [c|c m d Hm Hd].
  - assert (a'=b') by (eapply step_deterministic; eauto).
    subst b'; apply evstep_refl.
  - assert (m=a') by (eapply step_deterministic; eauto).
    subst m; eapply evstep_trans; [exact Hd|].
    eapply evstep_step; [exact Hb|apply evstep_refl].
Qed.
Lemma weak_N s t: weak s t -> segLL tm hN hN (rev t) s.
Proof.
  intros [F G] l r; unfold to_DH_config.
  eapply successor_path; [exact (G l r)|prove_step|prove_step].
Qed.
Lemma passive_wall p n:
  segRLs tm ([(hH,hN)]^^n) ([(hH,hN)]^^n) (tail_in p) (tail_in p).
Proof.
  destruct (tail_sound p) as [F G].
  eapply segRLs_wall; [exact F|apply weak_N,tail_sound].
Qed.

(* A binary digit is a two-to-one call transducer.  The first digit has the
   bare B/D interface, later digits have H/N.  No original-time arithmetic is
   part of these total-effect contracts. *)
Section BinaryCell.
Variables hR hL hR' hL': DH0.
Variables d0 d1 dt:list Sym.
Hypothesis Stop: segRL tm hR hL d0 d1.
Hypothesis Carry: segRR tm hR hR' d1 dt.
Hypothesis Back: segLL tm hL' hL dt d0.

Lemma cell_zero n:
  segRLs tm ([(hR,hL)]^^(n*2+1)) ([(hR',hL')]^^n) d0 d1.
Proof.
  induction n as [|n IH].
  - cbn; eapply segRLs_S; [exact Stop|constructor].
  - replace (S n*2+1) with (S(S(n*2+1))) by lia.
    cbn[lpow]; eapply segRLs_S; [exact Stop|].
    eapply segRLs_S'; [exact Carry|exact Back|exact IH].
Qed.
Lemma cell_one n:
  segRLs tm ([(hR,hL)]^^(n*2)) ([(hR',hL')]^^n) d1 d1.
Proof.
  destruct n as [|n]; [constructor|].
  replace (S n*2) with (S(n*2+1)) by lia.
  cbn[lpow]; eapply segRLs_S'; [exact Carry|exact Back|apply cell_zero].
Qed.
End BinaryCell.

Definition digit (b:bool) : list Sym := if b then [1;1;0;1;0;0] else [1;1;0;1;1;1].
Definition first_digit (b:bool) : list Sym := if b then [1;0;1;0;0] else [1;0;1;1;1].
Notation hB := (B,[]).
Notation hD := (D,[]).

Lemma digit_stop: segRL tm hH hN (digit false) (digit true).
Proof. unfold segRL,digit; intros; esx. Qed.
Lemma digit_carry: segRR tm hH hH (digit true) (rev [1;0;0;1;1;0]).
Proof. unfold segRR,digit; intros; esx. Qed.
Lemma digit_back: segLL tm hN hN (rev [1;0;0;1;1;0]) (digit false).
Proof. unfold segLL,digit; intros; esx. Qed.
Lemma first_stop: segRL tm hB hD (first_digit false) (first_digit true).
Proof. unfold segRL,first_digit; intros; esx. Qed.
Lemma first_carry: segRR tm hB hH (first_digit true) (rev [0;1;1;0]).
Proof. unfold segRR,first_digit; intros; esx. Qed.
Lemma first_back: segLL tm hN hD (rev [0;1;1;0]) (first_digit false).
Proof. unfold segLL,first_digit; intros; esx. Qed.
Lemma terminal: segRL tm hH hN [0;1;0;1] [0;1;0;0].
Proof. unfold segRL; intros; esx. Qed.

(* The left counter is a binary N, not a unary original-step count.  Its
   stream is oriented nearest the head first: separator0, low data bit, ... *)
Fixpoint left_positive (n:positive) : list Sym := match n with
  | xH=>[0;1]
  | xO p=>[0;0]++left_positive p
  | xI p=>[0;1]++left_positive p end.
Definition left_bits n := match n with N0=>[] | Npos p=>left_positive p end.
Definition left_side n := left_bits n *> 0inf.

Lemma left_zero: left_side 0%N=0inf.
Proof. reflexivity. Qed.
Lemma left_xO p: left_side (Npos(xO p))=0 >> 0 >> left_side (Npos p).
Proof. reflexivity. Qed.
Lemma left_xI p: left_side (Npos(xI p))=0 >> 1 >> left_side (Npos p).
Proof. reflexivity. Qed.
Lemma left_xH: left_side 1%N=0 >> 1 >> 0inf.
Proof. reflexivity. Qed.

Lemma counter_inc_positive p r:
  left_side (Npos p) <{{D}} r -->* left_side (Npos(Pos.succ p)) {{B}}> r.
Proof.
  revert r; induction p as [p IH|p IH|]; intro r.
  - cbn[Pos.succ left_side left_bits left_positive].
    simpl_tape; steps.
    eapply evstep_trans; [apply IH|].
    cbn[left_side left_bits left_positive]; esx.
  - cbn[Pos.succ left_side left_bits left_positive]; esx.
  - cbn[Pos.succ left_side left_bits left_positive]; esx.
Qed.
Lemma counter_inc n r:
  left_side n <{{D}} r -->* left_side (N.succ n) {{B}}> r.
Proof.
  destruct n as [|p]; [cbn[left_side left_bits N.succ left_positive]; esx|].
  apply counter_inc_positive.
Qed.
Lemma counter_inc_A n r:
  left_side n {{A}}> 1 >> r -->* left_side (N.succ n) {{B}}> 1 >> r.
Proof. step1; apply counter_inc. Qed.

(* Executable candidate.  Only binary N arithmetic is used by the left
   endpoint; the words between endpoints remain shared typed columns. *)
Inductive column := PW (b:bool) | PR (b:Sym) (body:sequence).
Inductive phase := Stable | Going.
Definition word p c := match p,c with
  | Stable,PW b=>W b | Going,PW b=>V b
  | Stable,PR b s=>box_in b (sequence_in s)
  | Going,PR b s=>[1]++box_prefix b (sequence_out s) end.
Definition words p := flat_map (word p).
Record deck := Deck { front:list column; back:list column; weight:N }.
Definition deck_words x := front x++rev(back x).
Definition empty_deck := Deck [] [] 0%N.
Definition deck_empty x := match front x,back x with [],[]=>true | _,_=>false end.
Definition deck_flip x := Deck (back x) (front x) (weight x).
Definition deck_push c x := Deck (front x) (c::back x) (N.succ(weight x)).
Definition deck_pop x := match front x with
  | c::f=>Some(c,Deck f (back x) (N.pred(weight x)))
  | []=>match fast_rev(back x) with []=>None
        | c::f=>Some(c,Deck f [] (N.pred(weight x))) end end.
Definition deck_join x y :=
  if N.leb(weight x)(weight y)
  then Deck (front x++fast_rev_append(back x)(front y)) (back y)
       (N.add(weight x)(weight y))
  else Deck (front x) (back y++fast_rev_append(front y)(back x))
       (N.add(weight x)(weight y)).
Definition directed_word d p c := match d with
  | R=>word p c | L=>fast_rev(word p c) end.
Definition band_bits d p x := flat_map (directed_word d p)(deck_words x).
Inductive token := Bit (b:Sym) | Band (p:phase)(x:deck) | Count (n:N).
Definition token_bits d u := match u with
  | Bit b=>[b] | Band p x=>band_bits d p x | Count n=>left_bits n end.
Definition stack_bits d s := flat_map(token_bits d)s.
Definition denote d s := stack_bits d s *> 0inf.
Definition phase_eq p q := match p,q with Stable,Stable | Going,Going=>true | _,_=>false end.
Definition put_band p x s := if deck_empty x then s else
  match s with Band q y::t=>
    if phase_eq p q then Band p(deck_join x y)::t else Band p x::s
  | _=>Band p x::s end.
Definition prepend_bits bs s := map Bit bs++s.
Definition count_stack n := match n with N0=>[] | _=>[Count n] end.
Definition twice_plus n b := match b with 0=>N.double n | 1=>N.succ_double n end.
Definition push_left b s := match b,s with
  | 0,[]=>[]
  | 0,Bit a::[]=>count_stack(twice_plus 0%N a)
  | 0,Bit a::Count n::[]=>count_stack(twice_plus n a)
  | _,_=>Bit b::s end.
Fixpoint push_lefts bs s := match bs with
  | []=>s | b::bs=>push_left b(push_lefts bs s) end.
Fixpoint pop d s : Sym*list token := match s with
  | []=>(0,[])
  | Bit b::s=>(b,s)
  | Count N0::s=>pop d s
  | Count(Npos p)::s=>match p with
      xH=>(0,Bit 1::s) | xO q=>(0,Bit 0::Count(Npos q)::s)
    | xI q=>(0,Bit 1::Count(Npos q)::s) end
  | Band p x::s=>match deck_pop x with
    | None=>pop d s
    | Some(c,y)=>match directed_word d p c with
      | []=>pop d s | b::bs=>(b,prepend_bits bs(put_band p y s)) end end end.
Fixpoint strip bs d s := match bs with
  | []=>Some s
  | b::bs=>let '(c,t):=pop d s in
    if Eqb.eqb b c then strip bs d t else None end.

(* The candidate parser is fuel bounded.  Its outer wrapper checks the exact
   represented input before using a candidate, so failure is only fallback.
   The recursive strong-body guard is retained, not inferred from parity. *)
Fixpoint sniff fuel s : option(column*list token) := match fuel with
  | O=>None | S k=>match s with
    | Band Stable x::t=>match deck_pop x with
      | Some(c,y)=>Some(c,put_band Stable y t) | None=>sniff k t end
    | Bit 0::Bit 1::Bit 0::Bit 0::t=>Some(PW false,t)
    | Bit 0::Bit 1::Bit 1::Bit 1::t=>Some(PW true,t)
    | Bit 1::Bit 1::t=>match sniff_sequence k t with
      | Some(body,b,u)=>Some(PR b body,u) | None=>None end
    | _=>None end end
with sniff_sequence fuel s : option(sequence*Sym*list token) := match fuel with
  | O=>None | S k=>match s with
    | Bit 1::Bit 1::Bit 0::Bit 1::Bit 0::Bit 0::t=>Some(SEmpty,0,t)
    | Bit 1::Bit 1::Bit 0::Bit 1::Bit 1::Bit 1::t=>Some(SEmpty,1,t)
    | _=>match sniff k s with
      | Some(PR b body,t)=>match sniff_tail k t with
        | Some(suffix,close,u)=>Some(SFrame b body suffix,close,u) | None=>None end
      | _=>None end end end
with sniff_tail fuel s : option(tail*Sym*list token) := match fuel with
  | O=>None | S k=>match s with
    | Bit 1::Bit 1::Bit 0::Bit 1::Bit 0::Bit 0::t=>Some(TEmpty,0,t)
    | Bit 1::Bit 1::Bit 0::Bit 1::Bit 1::Bit 1::t=>Some(TEmpty,1,t)
    | _=>match sniff k s with
      | Some(c,t)=>match sniff_tail k t with
        | Some(suffix,close,u)=>Some(match c with
            PW b=>TWord b suffix | PR b body=>TFrame b body suffix end,close,u)
        | None=>None end
      | None=>None end end end.
Definition parse s := match sniff 128 s with
  | None=>None
  | Some(c,_)=>match strip(word Stable c) R s with
    | None=>None | Some(t)=>Some(c,t) end end.
Fixpoint collect fuel x s := match fuel with
  | O=>(x,s)
  | S k=>match s with
    | Band Stable y::t=>collect k (deck_join x y) t
    | _=>match parse s with
      | Some(c,t)=>collect k(deck_push c x)t | None=>(x,s) end end end.
Definition discover s := match s with Band Stable _::_=>s | _=>
  let '(x,t):=collect 128 empty_deck s in put_band Stable x t end.

Definition left_value s := match s with []=>Some 0%N | [Count n]=>Some n | _=>None end.
Definition read_digit s := match s with
  | Bit 1::Bit 1::Bit 0::Bit 1::Bit 0::Bit 0::t=>Some(true,t)
  | Bit 1::Bit 1::Bit 0::Bit 1::Bit 1::Bit 1::t=>Some(false,t)
  | _=>None end.
Definition read_first s := match s with
  | Bit 1::Bit 0::Bit 1::Bit 0::Bit 0::t=>Some(true,t)
  | Bit 1::Bit 0::Bit 1::Bit 1::Bit 1::t=>Some(false,t)
  | _=>None end.
Fixpoint read_higher fuel s : list(deck*bool)*deck*list token := match fuel with
  | O=>([],empty_deck,s)
  | S k=>let '(gap,t):=collect 128 empty_deck s in
    match read_digit t with
    | None=>([],gap,t)
    | Some(b,u)=>let '(ds,last,v):=read_higher k u in ((gap,b)::ds,last,v) end end.
Fixpoint missing (ds:list(deck*bool)) := match ds with
  | []=>0%N | (_,b)::ds=>if b then N.double(missing ds) else N.succ_double(missing ds) end.
Fixpoint filled bit (ds:list(deck*bool)) rest := match ds with
  | []=>rest | (gap,_)::ds=>put_band Stable gap
      (prepend_bits(digit bit)(filled bit ds rest)) end.

Inductive config := Cfg (q:Q)(d:dir)(l r:list token).
Definition decode c := match c with Cfg q d l r=>match d with
  | L=>denote L l <{{q}} denote R r | R=>denote L l {{q}}> denote R r end end.
Definition raw c := match c with
  | Cfg q L l r=>let '(b,l'):=pop L l in match tm(q,b) with
    | None=>None | Some(w,L,q')=>Some(Cfg q' L l' (Bit w::r))
    | Some(w,R,q')=>Some(Cfg q' R (push_left w l') r) end
  | Cfg q R l r=>let '(b,r'):=pop R r in match tm(q,b) with
    | None=>None | Some(w,L,q')=>Some(Cfg q' L l(Bit w::r'))
    | Some(w,R,q')=>Some(Cfg q' R (push_left w l) r') end end.
Definition right_counter n r := match read_first r with
  | None=>None
  | Some(b,s)=>let '(ds,last,t):=read_higher 64 s in
    let m:=if b then N.double(missing ds) else N.succ_double(missing ds) in
    match strip [0;1;0;1] R t with
    | Some u=>Some(Cfg B R (count_stack(N.add n (N.succ m)))
        (prepend_bits(first_digit false)
          (filled false ds(put_band Stable last(prepend_bits[0;1;0;0]u)))))
    | None=>match m with N0=>None | _=>Some(Cfg B R (count_stack(N.add n m))
        (prepend_bits(first_digit true)(filled true ds(put_band Stable last t)))) end end end.
Definition h_macro l r := match strip [1] L l with
  | None=>None | Some l'=>match discover r with
    | Band Stable x::r'=>match strip [0;1;0;1] R r' with
      | Some t=>Some(Cfg A L l(put_band Stable x(prepend_bits[0;1;0;0]t)))
      | None=>Some(Cfg B R (Bit 1::put_band Going(deck_flip x)l') r') end
    | _=>None end end.
Definition g_macro l r := match strip [1] L l with
  | Some(Band Going x::l')=>Some(Cfg A L (Bit 1::l')(put_band Stable(deck_flip x)r))
  | _=>None end.
Definition n_macro l r := match l with
  | Band Going x::l'=>match strip [1] R r with
    | Some r'=>Some(Cfg D L l'(Bit 1::put_band Stable(deck_flip x)r'))
    | None=>None end | _=>None end.
Definition macro c := match c with
  | Cfg B R l r=>match left_value l with
    | Some n=>match right_counter n r with Some c'=>Some c' | None=>h_macro l r end
    | None=>h_macro l r end
  | Cfg D L l r=>match left_value l with
    | Some n=>Some(Cfg B R(count_stack(N.succ n))r) | None=>n_macro l r end
  | Cfg A R l (Bit 1::r)=>match left_value l with
    | Some n=>Some(Cfg B R(count_stack(N.succ n))(Bit 1::r)) | None=>None end
  | Cfg A L l r=>g_macro l r
  | _=>None end.
Definition advance c := match macro c with Some c'=>Some c' | None=>raw c end.
Definition then_config (o:option config)(f:config->option config) :=
  match o with None=>None | Some c=>f c end.
Fixpoint iterate_pos n c := match n with
  | xH=>advance c
  | xO n=>then_config(iterate_pos n c)(iterate_pos n)
  | xI n=>then_config(then_config(iterate_pos n c)(iterate_pos n))advance end.
Definition iterate n c := match n with N0=>Some c | Npos n=>iterate_pos n c end.
Definition check n := match iterate n(Cfg A R [] []) with None=>true | Some _=>false end.

Lemma column_sound c: weak (word Stable c)(word Going c).
Proof. destruct c; [apply weak_W|apply box_weak,sequence_sound]. Qed.
Lemma columns_sound cs: weak (words Stable cs)(words Going cs).
Proof. induction cs; [apply weak_empty|apply weak_app; [apply column_sound|exact IHcs]]. Qed.
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
Lemma deck_pop_spec x: match deck_pop x with None=>deck_words x=[]
  | Some(c,y)=>deck_words x=c::deck_words y end.
Proof.
  destruct x as [[|c f] b k]; unfold deck_pop,deck_words; cbn[front back weight].
  - rewrite fast_rev_spec; destruct (rev b) as [|c f] eqn:E; unfold deck_words;
      cbn[front back]; rewrite ?app_nil_r; reflexivity.
  - reflexivity.
Qed.
Lemma directed_word_nonempty d p c: directed_word d p c<>[].
Proof.
  assert (H:word p c<>[]) by (destruct p,c; cbn[word W V box_in box_prefix]; try destruct b; discriminate).
  destruct d; cbn[directed_word]; [|exact H].
  rewrite fast_rev_spec; intro E; apply H.
  apply (f_equal (@rev Sym)) in E; now rewrite rev_involutive in E.
Qed.
Lemma denote_bit d b s: denote d(Bit b::s)=b >> denote d s.
Proof. reflexivity. Qed.
Lemma denote_band d p x s: denote d(Band p x::s)=band_bits d p x *> denote d s.
Proof. unfold denote,stack_bits; cbn[flat_map token_bits]; apply Str_app_assoc. Qed.
Lemma denote_count d n s: denote d(Count n::s)=left_bits n *> denote d s.
Proof. unfold denote,stack_bits; cbn[flat_map token_bits]; apply Str_app_assoc. Qed.
Lemma count_stack_spec d n: denote d(count_stack n)=left_side n.
Proof. destruct n; unfold denote,stack_bits,count_stack,left_side; cbn; rewrite ?app_nil_r; reflexivity. Qed.
Lemma twice_plus_spec n b: left_side(twice_plus n b)=0 >> b >> left_side n.
Proof. destruct n as [|p],b; cbn; repeat rewrite <-const_unfold; reflexivity. Qed.
Lemma push_left_spec b s: denote L(push_left b s)=b >> denote L s.
Proof.
  destruct b; [|reflexivity].
  destruct s as [|[a|p x|n] s]; try reflexivity; [apply const_unfold|].
  destruct s as [|[a'|p x|n] s]; try reflexivity.
  - cbn[push_left]; rewrite count_stack_spec,twice_plus_spec; reflexivity.
  - destruct s; [|reflexivity]. cbn[push_left].
    rewrite count_stack_spec,twice_plus_spec,!denote_bit,denote_count; reflexivity.
Qed.
Lemma band_bits_join d p x y: band_bits d p(deck_join x y)=band_bits d p x++band_bits d p y.
Proof. unfold band_bits; rewrite deck_join_spec,flat_map_app; reflexivity. Qed.
Lemma band_bits_empty d p x: deck_empty x=true -> band_bits d p x=[].
Proof. intro H; unfold band_bits; rewrite (deck_empty_spec x H); reflexivity. Qed.
Lemma band_bits_R p x: band_bits R p x=words p(deck_words x).
Proof. reflexivity. Qed.
Lemma band_bits_flip p x: band_bits L p(deck_flip x)=rev(band_bits R p x).
Proof.
  unfold band_bits; rewrite deck_flip_spec.
  generalize(deck_words x); intro cs; induction cs as [|c cs IH]; [reflexivity|].
  cbn[rev]; rewrite flat_map_app; cbn[flat_map directed_word].
  rewrite fast_rev_spec,app_nil_r,IH,rev_app_distr; reflexivity.
Qed.
Lemma band_bits_L p x: band_bits L p x=rev(words p(deck_words(deck_flip x))).
Proof.
  replace x with (deck_flip(deck_flip x)) at 1 by (destruct x; reflexivity).
  rewrite band_bits_flip,band_bits_R; reflexivity.
Qed.
Lemma phase_eq_spec p q: phase_eq p q=true -> p=q.
Proof. destruct p,q; cbn; congruence. Qed.
Lemma put_band_spec d p x s: denote d(put_band p x s)=band_bits d p x *> denote d s.
Proof.
  unfold put_band; destruct(deck_empty x)eqn:E.
  - rewrite(band_bits_empty d p x E); reflexivity.
  - destruct s as [|[b|q y|n] s]; try apply denote_band.
    destruct(phase_eq p q)eqn:H; [apply phase_eq_spec in H; subst q|apply denote_band].
    unfold denote,stack_bits; cbn[flat_map token_bits].
    rewrite band_bits_join,!Str_app_assoc; reflexivity.
Qed.
Lemma prepend_bits_spec d bs s: denote d(prepend_bits bs s)=bs *> denote d s.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  change (denote d(Bit b::prepend_bits bs s)=b >> (bs *> denote d s)).
  now rewrite denote_bit,IH.
Qed.
Lemma pop_spec d s: denote d s=fst(pop d s) >> denote d(snd(pop d s)).
Proof.
  induction s as [|[b|p x|n] s IH]; [apply const_unfold|reflexivity| |].
  - pose proof(deck_pop_spec x)as E.
    cbn[pop]; destruct(deck_pop x)as [[c y]|]; cbn in E.
    + unfold denote,stack_bits at 1; cbn[flat_map token_bits]; unfold band_bits at 1.
      rewrite E; cbn[flat_map]; rewrite !Str_app_assoc.
      destruct(directed_word d p c)as [|b bs]eqn:H.
      * exfalso; exact(directed_word_nonempty d p c H).
      * change (b >> (bs *> band_bits d p y *> denote d s)=
          b >> denote d(prepend_bits bs(put_band p y s))).
        rewrite prepend_bits_spec,put_band_spec; reflexivity.
    + unfold denote,stack_bits at 1; cbn[flat_map token_bits]; unfold band_bits.
      rewrite E; cbn[flat_map Str_app]; exact IH.
  - destruct n as [|p]; [exact IH|destruct p; reflexivity].
Qed.
Lemma strip_spec bs d s t: strip bs d s=Some t -> denote d s=bs *> denote d t.
Proof.
  revert s; induction bs as [|b bs IH]; intros s E; cbn[strip]in E.
  - injection E as <-; reflexivity.
  - pose proof(pop_spec d s)as H; destruct(pop d s)as [c u]; cbn[fst snd]in H.
    destruct b,c; cbn in E; try discriminate; rewrite H,(IH _ E); reflexivity.
Qed.
Lemma parse_spec s c t: parse s=Some(c,t) -> denote R s=word Stable c *> denote R t.
Proof.
  unfold parse; destruct(sniff 128 s)as [[c' u]|]; [|discriminate].
  destruct(strip(word Stable c')R s)as [v|]eqn:E; [|discriminate].
  intro H; injection H as <- <-; apply strip_spec,E.
Qed.
Lemma collect_spec fuel x s:
  let '(y,t):=collect fuel x s in
  band_bits R Stable y *> denote R t=band_bits R Stable x *> denote R s.
Proof.
  revert x s; induction fuel as [|fuel IH]; intros x s; [reflexivity|].
  destruct s as [|[b|p y|n] s].
  - reflexivity.
  - cbn[collect]; destruct(parse(Bit b::s))as [[c t]|]eqn:E; [|reflexivity].
    specialize(IH(deck_push c x)t); destruct(collect fuel(deck_push c x)t)as [z u].
    cbn[fst snd] in IH; rewrite IH,(@parse_spec _ _ _ E); unfold band_bits;
      rewrite deck_push_spec,flat_map_app; cbn[flat_map directed_word];
      rewrite app_nil_r,Str_app_assoc; reflexivity.
  - destruct p; [|reflexivity]. cbn[collect].
    specialize(IH(deck_join x y)s); destruct(collect fuel(deck_join x y)s)as [z u].
    cbn[fst snd] in IH; rewrite IH,denote_band,band_bits_join,Str_app_assoc; reflexivity.
  - reflexivity.
Qed.
Lemma discover_spec s: denote R(discover s)=denote R s.
Proof.
  unfold discover; destruct s as [|[b|p x|n] s]; try destruct p; try reflexivity.
  pose proof(collect_spec 128 empty_deck(Bit b::s))as H.
  destruct(collect 128 empty_deck(Bit b::s))as [y t]; rewrite put_band_spec; exact H.
Qed.
Lemma left_value_spec s n: left_value s=Some n -> denote L s=left_side n.
Proof.
  destruct s as [|[b|p x|k] s]; cbn[left_value]; try discriminate.
  - intro H; injection H as <-; reflexivity.
  - destruct s; [|discriminate]; intro H; injection H as <-; rewrite denote_count; reflexivity.
Qed.

Definition gap_word x := band_bits R Stable x.
Fixpoint higher_in ds := match ds with
  | []=>[] | (g,b)::ds=>gap_word g++digit b++higher_in ds end.
Fixpoint higher_out b (ds:list(deck*bool)) := match ds with
  | []=>[] | (g,_)::ds=>gap_word g++digit b++higher_out b ds end.
Definition deficit (b:bool) n := if b then N.double n else N.succ_double n.
Lemma gap_wall x n:
  segRLs tm ([(hH,hN)]^^n) ([(hH,hN)]^^n) (gap_word x)(gap_word x).
Proof.
  destruct(columns_sound(deck_words x))as [F G].
  eapply segRLs_wall; [exact F|apply weak_N,columns_sound].
Qed.
Lemma digit_fill b n:
  segRLs tm ([(hH,hN)]^^N.to_nat(deficit b n)) ([(hH,hN)]^^N.to_nat n)
    (digit b)(digit true).
Proof.
  destruct b; unfold deficit; rewrite ?N2Nat.inj_double,?N2Nat.inj_succ_double.
  - rewrite Nat.mul_comm; eapply cell_one; [apply digit_stop|apply digit_carry|apply digit_back].
  - replace (S(2*N.to_nat n)) with (N.to_nat n*2+1) by lia.
    eapply cell_zero; [apply digit_stop|apply digit_carry|apply digit_back].
Qed.
Lemma first_fill b n:
  segRLs tm ([(hB,hD)]^^N.to_nat(deficit b n)) ([(hH,hN)]^^N.to_nat n)
    (first_digit b)(first_digit true).
Proof.
  destruct b; unfold deficit; rewrite ?N2Nat.inj_double,?N2Nat.inj_succ_double.
  - rewrite Nat.mul_comm; eapply cell_one; [apply first_stop|apply first_carry|apply first_back].
  - replace (S(2*N.to_nat n)) with (N.to_nat n*2+1) by lia.
    eapply cell_zero; [apply first_stop|apply first_carry|apply first_back].
Qed.
Lemma higher_fill ds:
  segRLs tm ([(hH,hN)]^^N.to_nat(missing ds)) [] (higher_in ds)(higher_out true ds).
Proof.
  induction ds as [|[g b]ds IH]; [constructor|].
  change (segRLs tm ([(hH,hN)]^^N.to_nat(deficit b(missing ds))) []
    (gap_word g++digit b++higher_in ds)(gap_word g++digit true++higher_out true ds)).
  eapply segRLs_concat; [apply gap_wall|].
  eapply segRLs_concat; [apply digit_fill|exact IH].
Qed.
Lemma higher_overflow ds last:
  segRLs tm [(hH,hN)] []
    (higher_out true ds++gap_word last++[0;1;0;1])
    (higher_out false ds++gap_word last++[0;1;0;0]).
Proof.
  induction ds as [|[g b]ds IH].
  - cbn[higher_out app].
    eapply segRLs_concat; [apply(gap_wall last 1)|].
    eapply segRLs_S; [apply terminal|constructor].
  - cbn[higher_out]; rewrite <-!app_assoc.
    eapply segRLs_concat; [apply(gap_wall g 1)|].
    eapply segRLs_concat; [|exact IH].
    eapply segRLs_S'; [apply digit_carry|apply digit_back|constructor].
Qed.
Lemma whole_fill b ds:
  segRLs tm ([(hB,hD)]^^N.to_nat(deficit b(missing ds))) []
    (first_digit b++higher_in ds)(first_digit true++higher_out true ds).
Proof. eapply segRLs_concat; [apply first_fill|apply higher_fill]. Qed.
Lemma whole_overflow ds last:
  segRLs tm [(hB,hD)] []
    (first_digit true++higher_out true ds++gap_word last++[0;1;0;1])
    (first_digit false++higher_out false ds++gap_word last++[0;1;0;0]).
Proof.
  eapply segRLs_concat; [|apply higher_overflow].
  eapply segRLs_S'; [apply first_carry|apply first_back|constructor].
Qed.
Lemma whole_terminal b ds last:
  segRLs tm ([(hB,hD)]^^N.to_nat(N.succ(deficit b(missing ds)))) []
    (first_digit b++higher_in ds++gap_word last++[0;1;0;1])
    (first_digit false++higher_out false ds++gap_word last++[0;1;0;0]).
Proof.
  rewrite N2Nat.inj_succ.
  replace (S(N.to_nat(deficit b(missing ds)))) with
    (N.to_nat(deficit b(missing ds))+1) by lia.
  rewrite lpow_add.
  change (segRLs tm (([(hB,hD)]^^N.to_nat(deficit b(missing ds)))++[(hB,hD)]) ([]++[])
    (first_digit b++higher_in ds++gap_word last++[0;1;0;1])
    (first_digit false++higher_out false ds++gap_word last++[0;1;0;0])).
  eapply segRLs_trans; [|apply whole_overflow].
  rewrite !app_assoc.
  eapply segRLs_concat; [|constructor].
  eapply segRLs_concat; [apply whole_fill|constructor].
Qed.
Lemma service_counter k n r1 r2:
  sideRLs tm ([(hB,hD)]^^k) r1 r2 ->
  left_side n {{B}}> r1 -->* left_side(N.add n(N.of_nat k)) {{B}}> r2.
Proof.
  revert n r1 r2; induction k as [|k IH]; intros n r1 r2 H.
  - inversion H; subst; rewrite N.add_0_r; apply evstep_refl.
  - cbn[lpow]in H.
    inversion H as [|h1 h2 u v w hs Hr Hs]; subst.
    eapply evstep_trans; [apply progress_evstep,Hr|].
    eapply evstep_trans; [apply counter_inc|].
    replace (N.add n(N.of_nat(S k))) with (N.add(N.succ n)(N.of_nat k)) by lia.
    apply IH; exact Hs.
Qed.
Lemma services_from_segment n m w1 w2 r:
  segRLs tm ([(hB,hD)]^^N.to_nat m) [] w1 w2 ->
  left_side n {{B}}> w1 *> r -->* left_side(N.add n m) {{B}}> w2 *> r.
Proof.
  intro H; rewrite <-(N2Nat.id m).
  apply service_counter; eapply segRLs_sideRLs_concat; [exact H|constructor].
Qed.
Lemma read_digit_spec s b t: read_digit s=Some(b,t) -> denote R s=digit b *> denote R t.
Proof.
  unfold read_digit.
  do 6 (destruct s as [|[a|p x|n] s]; try discriminate; try destruct a; try discriminate);
    intro H; injection H as <- <-; reflexivity.
Qed.
Lemma read_first_spec s b t: read_first s=Some(b,t) -> denote R s=first_digit b *> denote R t.
Proof.
  unfold read_first.
  do 5 (destruct s as [|[a|p x|n] s]; try discriminate; try destruct a; try discriminate);
    intro H; injection H as <- <-; reflexivity.
Qed.
Lemma read_higher_spec fuel s:
  let '(ds,last,t):=read_higher fuel s in
  denote R s=higher_in ds *> gap_word last *> denote R t.
Proof.
  revert s; induction fuel as [|fuel IH]; intro s; [reflexivity|].
  cbn[read_higher]; pose proof(collect_spec 128 empty_deck s)as H.
  destruct(collect 128 empty_deck s)as [g t]; cbn[fst snd] in H.
  change (gap_word g *> denote R t=denote R s) in H.
  destruct(read_digit t)as [[b u]|]eqn:E.
  - specialize(IH u); destruct(read_higher fuel u)as [[ds last]v]; cbn[fst snd] in IH.
    rewrite <-H,(@read_digit_spec _ _ _ E),IH; cbn[higher_in].
    rewrite !Str_app_assoc; reflexivity.
  - rewrite <-H; reflexivity.
Qed.
Lemma filled_spec b ds s:
  denote R(filled b ds s)=higher_out b ds *> denote R s.
Proof.
  induction ds as [|[g a]ds IH]; [reflexivity|].
  cbn[filled higher_out]; rewrite put_band_spec,prepend_bits_spec,IH,!Str_app_assoc; reflexivity.
Qed.
Lemma right_counter_spec n r c:
  right_counter n r=Some c -> left_side n {{B}}> denote R r -->* decode c.
Proof.
  unfold right_counter; destruct(read_first r)as [[b s]|]eqn:E; [|discriminate].
  pose proof(read_higher_spec 64 s)as Hs.
  destruct(read_higher 64 s)as [[ds last]t]; cbn[fst snd] in Hs.
  intro K.
  set (m:=deficit b(missing ds)).
  change ((match strip [0;1;0;1] R t with
    | Some u=>Some(Cfg B R(count_stack(N.add n(N.succ m)))
      (prepend_bits(first_digit false)(filled false ds(put_band Stable last(prepend_bits[0;1;0;0]u)))))
    | None=>match m with N0=>None | _=>Some(Cfg B R(count_stack(N.add n m))
      (prepend_bits(first_digit true)(filled true ds(put_band Stable last t)))) end end)=Some c) in K.
  destruct(strip [0;1;0;1] R t)as [u|]eqn:T.
  - injection K as <-; cbn[decode].
    rewrite count_stack_spec,prepend_bits_spec,filled_spec,put_band_spec,prepend_bits_spec.
    rewrite (@read_first_spec _ _ _ E),Hs,(@strip_spec _ _ _ _ T).
    rewrite <-!Str_app_assoc.
    apply services_from_segment; rewrite <-!app_assoc; apply whole_terminal.
  - destruct m as [|p]eqn:M; [discriminate|].
    injection K as <-; cbn[decode].
    rewrite count_stack_spec,prepend_bits_spec,filled_spec,put_band_spec.
    rewrite (@read_first_spec _ _ _ E),Hs.
    rewrite <-!Str_app_assoc.
    apply services_from_segment.
    unfold m in M; rewrite <-M.
    eapply segRLs_concat; [apply whole_fill|constructor].
Qed.

Lemma columns_reflect cs l r:
  l << 1 {{B}}> words Stable cs *> [0;1;0;1] *> r -->*
  l << 1 <{{A}} words Stable cs *> [0;1;0;0] *> r.
Proof.
  destruct(columns_sound cs)as [F G].
  eapply evstep_trans; [apply F|].
  eapply evstep_trans; [apply progress_evstep,H_reflect|apply G].
Qed.
Lemma h_macro_spec l r c: h_macro l r=Some c -> decode(Cfg B R l r) -->* decode c.
Proof.
  unfold h_macro; destruct(strip [1] L l)as [l'|]eqn:HL; [|discriminate].
  pose proof(discover_spec r)as HR.
  destruct(discover r)as [|[b|p x|n]r']eqn:E; try discriminate.
  destruct p; [|discriminate].
  rewrite denote_band in HR.
  destruct(strip [0;1;0;1] R r')as [t|]eqn:T;
    intro H; injection H as <-; cbn[decode].
  - rewrite put_band_spec,prepend_bits_spec,(@strip_spec _ _ _ _ HL),<-HR.
    rewrite (@strip_spec _ _ _ _ T); apply columns_reflect.
  - rewrite denote_bit,put_band_spec,band_bits_flip.
    rewrite (@strip_spec _ _ _ _ HL),<-HR; apply(proj1(columns_sound(deck_words x))).
Qed.
Lemma g_macro_spec l r c: g_macro l r=Some c -> decode(Cfg A L l r) -->* decode c.
Proof.
  unfold g_macro; destruct(strip [1] L l)as [t|]eqn:E; [|discriminate].
  destruct t as [|[b|p x|n]l']; try discriminate; destruct p; [discriminate|].
  intro H; injection H as <-; cbn[decode].
  rewrite (@strip_spec _ _ _ _ E),denote_band,denote_bit,put_band_spec,band_bits_L.
  apply(proj2(columns_sound(deck_words(deck_flip x)))).
Qed.
Lemma n_macro_spec l r c: n_macro l r=Some c -> decode(Cfg D L l r) -->* decode c.
Proof.
  unfold n_macro; destruct l as [|[b|p x|n]l']; try discriminate; destruct p; [discriminate|].
  destruct(strip [1] R r)as [r'|]eqn:E; [|discriminate].
  intro H; injection H as <-; cbn[decode].
  rewrite denote_band,denote_bit,put_band_spec,band_bits_L,(@strip_spec _ _ _ _ E).
  apply weak_N,columns_sound.
Qed.
Lemma macro_spec c c': macro c=Some c' -> decode c -->* decode c'.
Proof.
  destruct c as [q d l r]; destruct q,d; cbn[macro]; try discriminate.
  - apply g_macro_spec.
  - destruct r as [|[b|p x|n]r]; try discriminate; destruct b; [discriminate|].
    destruct(left_value l)as [k|]eqn:E; [|discriminate].
    intro H; injection H as <-; cbn[decode].
    rewrite (@left_value_spec _ _ E),count_stack_spec,!denote_bit; apply counter_inc_A.
  - destruct(left_value l)as [k|]eqn:E; [|apply h_macro_spec].
    destruct(right_counter k r)as [u|]eqn:K; [|apply h_macro_spec].
    intro H; injection H as <-; cbn[decode].
    rewrite (@left_value_spec _ _ E); apply right_counter_spec,K.
  - destruct(left_value l)as [k|]eqn:E; [|apply n_macro_spec].
    intro H; injection H as <-; cbn[decode].
    rewrite (@left_value_spec _ _ E),count_stack_spec; apply counter_inc.
Qed.
Definition transfer c o := match o with
  | None=>halts tm(decode c)
  | Some c'=>halts tm(decode c') -> halts tm(decode c) end.
Lemma raw_spec c: transfer c(raw c).
Proof.
  destruct c as [q [|]l r]; unfold raw; cbn[decode].
  - pose proof(pop_spec L l)as H; destruct(pop L l)as [b l']; cbn[fst snd]in H.
    unfold transfer; cbn[decode]; rewrite H; cbn[hd tl].
    destruct(tm(q,b))as [[[w d]q']|]eqn:E.
    + destruct d; cbn[decode]; rewrite ?denote_bit,?push_left_spec; intro K.
      * eapply halts_evstep; [exact K|apply progress_evstep,progress_base].
        exact(@step_left tm q q' b w(denote L l')(denote R r)E).
      * eapply halts_evstep; [exact K|apply progress_evstep,progress_base].
        exact(@step_right tm q q' b w(denote L l')(denote R r)E).
    + apply halted_halts; exact E.
  - pose proof(pop_spec R r)as H; destruct(pop R r)as [b r']; cbn[fst snd]in H.
    unfold transfer; cbn[decode]; rewrite H; cbn[hd tl].
    destruct(tm(q,b))as [[[w d]q']|]eqn:E.
    + destruct d; cbn[decode]; rewrite ?denote_bit,?push_left_spec; intro K.
      * eapply halts_evstep; [exact K|apply progress_evstep,progress_base].
        exact(@step_left tm q q' b w(denote L l)(denote R r')E).
      * eapply halts_evstep; [exact K|apply progress_evstep,progress_base].
        exact(@step_right tm q q' b w(denote L l)(denote R r')E).
    + apply halted_halts; exact E.
Qed.
Lemma advance_spec c: transfer c(advance c).
Proof.
  unfold advance; destruct(macro c)as [c'|]eqn:E; [|apply raw_spec].
  unfold transfer; intro H; eapply halts_evstep; [exact H|apply macro_spec,E].
Qed.
Lemma bind_spec c o f:
  transfer c o -> (forall c',transfer c'(f c')) -> transfer c(then_config o f).
Proof.
  destruct o as [c'|]; cbn[then_config transfer]; auto.
  intros H K; specialize(K c'); destruct(f c'); cbn[transfer]in *; tauto.
Qed.
Lemma iterate_pos_spec n c: transfer c(iterate_pos n c).
Proof.
  revert c; induction n; intro c; cbn[iterate_pos].
  - apply bind_spec; [apply bind_spec; apply IHn|apply advance_spec].
  - apply bind_spec; apply IHn.
  - apply advance_spec.
Qed.
Lemma iterate_spec n c: transfer c(iterate n c).
Proof. destruct n; cbn[iterate transfer]; [trivial|apply iterate_pos_spec]. Qed.
Lemma check_spec n: check n=true -> halts tm c0.
Proof.
  pose proof(iterate_spec n(Cfg A R [] []))as H.
  unfold check; destruct(iterate n(Cfg A R [] [])); [discriminate|].
  intro E; exact H.
Qed.

Theorem halt: halts tm c0.
Proof. apply(@check_spec 20000000000%N). native_check_eq. Time Qed.

End TM.

Print Assumptions TM.halt.
