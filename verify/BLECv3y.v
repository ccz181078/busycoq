From BusyCoq Require Import
  Individual62 Longitudinal LongN InfiniteRect ES_v3.
Require Import
  ZifyNat Lia ZArith String Ascii List Wf_nat Compare_dec PeanoNat Bool
  FunctionalExtensionality.

Open Scope list.

Fixpoint multistep_c' tm n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm n3 c
  | S n1 =>
      match multistep_c tm n2 c with
      | Some c' => multistep_c' tm n1 n2 n3 c'
      | None => None
      end
  end.

Lemma multistep_c'_spec tm n1 n2 n3 c c':
  multistep_c' tm n1 n2 n3 c = Some c' <->
  c -[ tm ]->> (n1*n2+n3) / c'.
Proof.
  revert c c'; induction n1; cbn [multistep_c']; intros.
  - apply multistep_c_spec.
  - destruct (multistep_c tm n2 c) eqn:E.
    + apply multistep_c_spec in E.
      rewrite IHn1.
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      split; intro H.
      * eapply multistep_trans; eauto.
      * eapply rewind_split in H.
        destruct H as [c'0 [I1 I2]].
        multistep_deterministic; eauto.
    + split; [congruence|].
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      intro H; eapply rewind_split in H.
      destruct H as [c'0 [I1 I2]].
      apply multistep_c_spec in I1; congruence.
Qed.

Ltac native_check_eq :=
  match goal with
  | |- _ = ?a => native_cast_no_check (eq_refl a)
  end.

(* Compact text representation for the finite dotted-edge certificates.
   The strings are merely data: [edge_group_sound] below interprets them as
   actual directed heads and tape words, after which the machine-specific
   proof checks [sideRLs] against the original TM. *)
Record edge_group_text : Type := mk_edge_group_text {
  edge_group_before : string;
  edge_group_consume : string;
  edge_group_emit : string;
  edge_group_after : string
}.

Fixpoint bit_word_of_string (s:string) : list Sym :=
  match s with
  | EmptyString => []
  | String a s' =>
      (if Nat.eqb (nat_of_ascii a) 48 then 0 else 1) ::
        bit_word_of_string s'
  end.

Fixpoint signal_word_of_string {A:Type}
    (hash atsig dollar:list A) (s:string) : list A :=
  match s with
  | EmptyString => []
  | String a s' =>
      let token :=
        if Nat.eqb (nat_of_ascii a) 35 then hash
        else if Nat.eqb (nat_of_ascii a) 64 then atsig
        else dollar in
      token ++ signal_word_of_string hash atsig dollar s'
  end.

Fixpoint column_word_of_string (x y:list Sym) (s:string) : list Sym :=
  match s with
  | EmptyString => []
  | String a s' =>
      (if Nat.eqb (nat_of_ascii a) 88 then x else y) ++
        column_word_of_string x y s'
  end.

Definition edge_group_sound tm hash atsig dollar x y
    (g:edge_group_text) : Prop :=
  sideRLs tm
    (signal_word_of_string hash atsig dollar (edge_group_consume g))
    (bit_word_of_string (edge_group_before g) *> 0inf)
    (column_word_of_string x y (edge_group_emit g) *>
      (bit_word_of_string (edge_group_after g) *> 0inf)).

Inductive packet_marker := PacketAt | PacketDollar.

Record packet_stream_text : Type := mk_packet_stream_text {
  packet_stream_prefix : string;
  packet_stream_marker : packet_marker;
  packet_stream_start : nat
}.

Record edge_phase_text : Type := mk_edge_phase_text {
  edge_phase_group : edge_group_text;
  edge_phase_stream : packet_stream_text;
  edge_phase_tail : packet_stream_text;
  edge_phase_next_stream : packet_stream_text
}.

Inductive column_symbol := ColumnX | ColumnY.

(* A materialized column is completely specified, for closure purposes, by
   its stationary X/Y word and its infinite input stream.  The output stream
   is retained in the certificate so adjacent columns can be joined without
   choosing a synchronized global time slice. *)
Record column_flow_text : Type := mk_column_flow_text {
  column_flow_symbol : column_symbol;
  column_flow_input : packet_stream_text;
  column_flow_output : packet_stream_text
}.

(* Finite initialization cuts may contain transient H/D/P/Q columns in
   addition to the periodic X/Y alphabet. *)
Inductive ordinary_column_symbol :=
| OrdinaryX | OrdinaryY | OrdinaryH
| OrdinaryD | OrdinaryP | OrdinaryQ.

Fixpoint column_symbols_of_string (s:string) : list column_symbol :=
  match s with
  | EmptyString => []
  | String a s' =>
      (if Nat.eqb (nat_of_ascii a) 88 then ColumnX else ColumnY) ::
        column_symbols_of_string s'
  end.

Fixpoint column_flows_linked (fs:list column_flow_text) : Prop :=
  match fs with
  | [] | [_] => True
  | f::((g::_) as fs') =>
      column_flow_output f = column_flow_input g /\
      column_flows_linked fs'
  end.

Fixpoint partition_phase_columns (ps:list edge_phase_text)
    (fs:list column_flow_text) : list (list column_flow_text) :=
  match ps with
  | [] => []
  | p::ps' =>
      firstn (String.length (edge_group_emit (edge_phase_group p))) fs ::
      partition_phase_columns ps'
        (skipn (String.length (edge_group_emit (edge_phase_group p))) fs)
  end.

Definition default_column_flow : column_flow_text :=
  mk_column_flow_text ColumnX
    (mk_packet_stream_text EmptyString PacketAt 0)
    (mk_packet_stream_text EmptyString PacketAt 0).

Definition phase_columns_match (p:edge_phase_text)
    (fs:list column_flow_text) : Prop :=
  fs <> [] /\
  column_flow_input (hd default_column_flow fs) = edge_phase_tail p /\
  column_flow_output (last fs default_column_flow) =
    edge_phase_next_stream p /\
  column_flows_linked fs /\
  map column_flow_symbol fs =
    column_symbols_of_string (edge_group_emit (edge_phase_group p)).

Lemma Forall_firstn_local {A} (P:A->Prop) n xs:
  Forall P xs -> Forall P (firstn n xs).
Proof.
  intros H; revert n; induction H as [|x ys Hx Hys IH];
    intros [|n]; cbn.
  - constructor.
  - constructor.
  - constructor.
  - constructor; [exact Hx|apply IH].
Qed.

Lemma Forall_skipn_local {A} (P:A->Prop) n xs:
  Forall P xs -> Forall P (skipn n xs).
Proof.
  intros H; revert n; induction H; intros [|n]; cbn; auto.
Qed.

Lemma Forall_rotate_local {A} (P:A->Prop) d xs:
  xs <> [] -> Forall P xs ->
  Forall P (tl xs ++ [hd d xs]).
Proof.
  intros Hne H; destruct xs as [|x xs]; [contradiction|].
  inversion H; subst; cbn.
  apply Forall_app; split; [assumption|constructor; auto].
Qed.

Lemma partition_phase_columns_Forall {P}
    (ps:list edge_phase_text) fs:
  Forall P fs ->
  Forall (Forall P) (partition_phase_columns ps fs).
Proof.
  revert fs. induction ps as [|p ps IH]; intros fs Hfs; cbn.
  - constructor.
  - constructor.
    + apply Forall_firstn_local; exact Hfs.
    + apply IH, Forall_skipn_local; exact Hfs.
Qed.

Lemma Forall2_In_left_exists {A B} (R:A->B->Prop) xs ys x:
  Forall2 R xs ys -> In x xs ->
  exists y, In y ys /\ R x y.
Proof.
  intros H; induction H; cbn; intros Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists y. split; [left; reflexivity|assumption].
    + destruct (IHForall2 Hin) as [z [Hz HRz]].
      exists z. split; [right; exact Hz|exact HRz].
Qed.

(* An increasing packet stream.  [packet_stream ordinary special r f]
   starts with [ordinary^r special]; [f 0], [f 1], ... are the lengths of
   the following ordinary runs.  Keeping [r] separate represents all [V]
   suffixes, including the cases where two special signals are close. *)
CoFixpoint packet_stream {A : Type} (ordinary special:A)
    (r:nat) (f:nat->nat) : Stream A :=
  match r with
  | O => [special] *> packet_stream ordinary special (f O)
      (fun n => f (S n))
  | S r' => [ordinary] *> packet_stream ordinary special r' f
  end.

Definition growing_packets {A : Type} (ordinary special:A) (k:nat) :
    Stream A :=
  packet_stream ordinary special k (fun n => k+S n).

Definition stream_of_text {A:Type} (hash atsig dollar:A)
    (d:packet_stream_text) : Stream A :=
  signal_word_of_string [hash] [atsig] [dollar]
      (packet_stream_prefix d) *>
    growing_packets hash
      (match packet_stream_marker d with
       | PacketAt => atsig | PacketDollar => dollar end)
      (packet_stream_start d).

(* A symbolic head element of a packet stream.  The parser deliberately
   agrees with [signal_word_of_string]: every character other than [#] and
   [@] denotes the dollar signal. *)
Inductive packet_signal :=
| PacketHash
| PacketAtSignal
| PacketDollarSignal.

Definition packet_signal_of_ascii (a:ascii) : packet_signal :=
  if Nat.eqb (nat_of_ascii a) 35 then PacketHash
  else if Nat.eqb (nat_of_ascii a) 64 then PacketAtSignal
  else PacketDollarSignal.

Definition packet_marker_signal (m:packet_marker) : packet_signal :=
  match m with
  | PacketAt => PacketAtSignal
  | PacketDollar => PacketDollarSignal
  end.

Definition packet_signal_value {A:Type} (hash atsig dollar:A)
    (s:packet_signal) : A :=
  match s with
  | PacketHash => hash
  | PacketAtSignal => atsig
  | PacketDollarSignal => dollar
  end.

Definition packet_marker_ascii (m:packet_marker) : ascii :=
  match m with
  | PacketAt => ascii_of_nat 64
  | PacketDollar => ascii_of_nat 36
  end.

Fixpoint hash_string_before (n:nat) (tail:string) : string :=
  match n with
  | O => tail
  | S n' => String (ascii_of_nat 35) (hash_string_before n' tail)
  end.

(* Pop one signal while retaining a finite descriptor for the remaining
   suffix.  In the last branch the head lies inside a generated [#]-run;
   its rest is made explicit up to the separator, after which the next
   growing packet starts two larger than [n]. *)
Definition packet_stream_text_pop (d:packet_stream_text)
    : packet_signal * packet_stream_text :=
  match packet_stream_prefix d with
  | String a s' =>
      (packet_signal_of_ascii a,
       mk_packet_stream_text s' (packet_stream_marker d)
         (packet_stream_start d))
  | EmptyString =>
      match packet_stream_start d with
      | O =>
          (packet_marker_signal (packet_stream_marker d),
           mk_packet_stream_text EmptyString (packet_stream_marker d) 1)
      | S n =>
          (PacketHash,
           mk_packet_stream_text
             (hash_string_before n
               (String (packet_marker_ascii (packet_stream_marker d))
                 EmptyString))
             (packet_stream_marker d) (S (S n)))
      end
  end.

Lemma repeat_singleton_lpow {A} (a:A) n:
  repeat a n = [a]^^n.
Proof.
  induction n; [reflexivity|].
  cbn [repeat lpow]; rewrite IHn; reflexivity.
Qed.

Lemma lpow_S_right {A} (xs:list A) n:
  xs^^(S n) = (xs^^n)++xs.
Proof. rewrite lpow_S, <- lpow_shift. reflexivity. Qed.

Lemma packet_stream_S {A} (ordinary special:A) r f:
  packet_stream ordinary special (S r) f =
  [ordinary] *> packet_stream ordinary special r f.
Proof.
  rewrite (Cons_unfold _ (packet_stream ordinary special (S r) f)) at 1.
  reflexivity.
Qed.

Lemma packet_stream_0 {A} (ordinary special:A) f:
  packet_stream ordinary special 0 f =
  [special] *> packet_stream ordinary special (f O) (fun n=>f (S n)).
Proof.
  rewrite (Cons_unfold _ (packet_stream ordinary special 0 f)) at 1.
  reflexivity.
Qed.

Lemma packet_stream_add {A} (ordinary special:A) k r f:
  packet_stream ordinary special (k+r) f =
  repeat ordinary k *> packet_stream ordinary special r f.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - cbn [Nat.add repeat]; rewrite packet_stream_S,IH; reflexivity.
Qed.

Lemma packet_stream_packet {A} (ordinary special:A) r f:
  packet_stream ordinary special r f =
  (repeat ordinary r++[special]) *>
    packet_stream ordinary special (f O) (fun n=>f (S n)).
Proof.
  replace (packet_stream ordinary special r f) with
    (packet_stream ordinary special (r+0) f) by (f_equal; lia).
  rewrite packet_stream_add,packet_stream_0,Str_app_assoc; reflexivity.
Qed.

Lemma growing_packets_unfold {A} (ordinary special:A) k:
  growing_packets ordinary special k =
  (repeat ordinary k++[special]) *>
    growing_packets ordinary special (S k).
Proof.
  unfold growing_packets at 1.
  rewrite packet_stream_packet.
  unfold growing_packets.
  replace (k+1) with (S k) by lia.
  assert (Ef:(fun n:nat=>k+S (S n))=(fun n:nat=>S k+S n)).
  { extensionality n; lia. }
  rewrite Ef; reflexivity.
Qed.

Lemma signal_word_hash_string_before {A} (hash atsig dollar:A) n m:
  signal_word_of_string [hash] [atsig] [dollar]
    (hash_string_before n (String (packet_marker_ascii m) EmptyString)) =
  repeat hash n ++
    [match m with PacketAt => atsig | PacketDollar => dollar end].
Proof.
  destruct m; induction n as [|n IH];
    cbn [hash_string_before packet_marker_ascii
      signal_word_of_string repeat] in *;
    rewrite ?IH; reflexivity.
Qed.

Lemma packet_stream_text_pop_sound {A} (hash atsig dollar:A) d s d':
  packet_stream_text_pop d = (s,d') ->
  stream_of_text hash atsig dollar d =
    [packet_signal_value hash atsig dollar s] *>
      stream_of_text hash atsig dollar d'.
Proof.
  destruct d as [prefix marker start].
  destruct prefix as [|a prefix].
  - destruct start as [|n].
    + destruct marker; cbn [packet_stream_text_pop] ; intro H;
        inversion H; subst; clear H;
        unfold stream_of_text; cbn [signal_word_of_string
          packet_marker_signal packet_signal_value];
        rewrite growing_packets_unfold; reflexivity.
    + cbn [packet_stream_text_pop]; intro H.
      inversion H; subst; clear H.
      unfold stream_of_text; cbn [signal_word_of_string packet_signal_value].
      rewrite growing_packets_unfold.
      cbn [packet_stream_prefix packet_stream_marker
        packet_stream_start].
      rewrite signal_word_hash_string_before.
      destruct marker; cbn [repeat];
        repeat rewrite <- Str_app_assoc; reflexivity.
  - cbn [packet_stream_text_pop]; intro H.
    inversion H; subst; clear H.
    unfold stream_of_text at 1; cbn [signal_word_of_string].
    cbn [packet_stream_prefix packet_stream_marker packet_stream_start].
    cbn [signal_word_of_string].
    unfold packet_signal_of_ascii.
    destruct (Nat.eqb (nat_of_ascii a) 35); [reflexivity|].
    destruct (Nat.eqb (nat_of_ascii a) 64); reflexivity.
Qed.

Definition packet_signal_eqb (a b:packet_signal) : bool :=
  match a,b with
  | PacketHash, PacketHash
  | PacketAtSignal, PacketAtSignal
  | PacketDollarSignal, PacketDollarSignal => true
  | _,_ => false
  end.

Lemma packet_signal_eqb_eq a b:
  packet_signal_eqb a b = true <-> a = b.
Proof. destruct a,b; cbn; split; intro H; try discriminate; reflexivity. Qed.

Fixpoint packet_stream_text_consume (input:string)
    (d:packet_stream_text) : option packet_stream_text :=
  match input with
  | EmptyString => Some d
  | String a input' =>
      let '(s,d') := packet_stream_text_pop d in
      if packet_signal_eqb (packet_signal_of_ascii a) s
      then packet_stream_text_consume input' d'
      else None
  end.

Definition packet_stream_text_eq_dec (a b:packet_stream_text) :
    {a=b}+{a<>b}.
Proof.
  decide equality; [apply Nat.eq_dec|decide equality|apply string_dec].
Defined.

Definition packet_stream_text_eqb (a b:packet_stream_text) : bool :=
  if packet_stream_text_eq_dec a b then true else false.

Lemma packet_stream_text_eqb_eq a b:
  packet_stream_text_eqb a b = true <-> a=b.
Proof.
  unfold packet_stream_text_eqb.
  destruct (packet_stream_text_eq_dec a b); split; intro H;
    try reflexivity; try discriminate; congruence.
Qed.

Definition edge_phase_consume_check (p:edge_phase_text) : bool :=
  match packet_stream_text_consume
      (edge_group_consume (edge_phase_group p))
      (edge_phase_stream p) with
  | Some d => packet_stream_text_eqb d (edge_phase_tail p)
  | None => false
  end.

Lemma edge_phase_consume_check_sound p:
  edge_phase_consume_check p = true ->
  packet_stream_text_consume
    (edge_group_consume (edge_phase_group p))
    (edge_phase_stream p) = Some (edge_phase_tail p).
Proof.
  unfold edge_phase_consume_check.
  destruct (packet_stream_text_consume
    (edge_group_consume (edge_phase_group p))
    (edge_phase_stream p)) as [d|] eqn:E; [|discriminate].
  intro H; apply packet_stream_text_eqb_eq in H; subst d; reflexivity.
Qed.

Lemma forallb_sound {A} (check:A->bool) (P:A->Prop) xs:
  (forall x, check x = true -> P x) ->
  forallb check xs = true -> Forall P xs.
Proof.
  intros Hsound; induction xs as [|x xs IH]; cbn; intro H.
  - constructor.
  - apply Bool.andb_true_iff in H; destruct H as [Hx Hxs].
    constructor; [apply Hsound; exact Hx|apply IH; exact Hxs].
Qed.

Lemma packet_stream_text_consume_sound {A} (hash atsig dollar:A)
    input d d':
  packet_stream_text_consume input d = Some d' ->
  stream_of_text hash atsig dollar d =
    signal_word_of_string [hash] [atsig] [dollar] input *>
      stream_of_text hash atsig dollar d'.
Proof.
  revert d d'.
  induction input as [|a input IH]; intros d d' H.
  - cbn [packet_stream_text_consume] in H; inversion H; reflexivity.
  - cbn [packet_stream_text_consume] in H.
    destruct (packet_stream_text_pop d) as [s tail] eqn:E.
    destruct (packet_signal_eqb (packet_signal_of_ascii a) s)
      eqn:Es; [|discriminate].
    apply packet_signal_eqb_eq in Es; subst s.
    rewrite (packet_stream_text_pop_sound hash atsig dollar d
      (packet_signal_of_ascii a) tail E).
    rewrite (IH tail d' H).
    cbn [signal_word_of_string].
    unfold packet_signal_of_ascii, packet_signal_value.
    destruct (Nat.eqb (nat_of_ascii a) 35); [reflexivity|].
    destruct (Nat.eqb (nat_of_ascii a) 64); reflexivity.
Qed.

(* A dynamic right edge is not a static infinite rectangle: it first consumes
   a finite prefix [hs] of its input stream and only then materializes the
   nonempty word [w] immediately to its left.  The remaining stream crosses
   [w] column by column.  This is the shape of a dotted TM4 edge rule. *)
Definition dynamic_side_step tm
    (P : Stream (DH0*DH0) -> side -> Prop)
    (L : Stream (DH0*DH0)) (top : side) : Prop :=
  exists hs Ltail Ledge top' w width,
    0 < width /\
    w <> [] /\
    L = hs *> Ltail /\
    sideRLs tm hs top (w *> top') /\
    downRect tm Ltail Ledge w width /\
    P Ledge top'.

(* This is the [sideRLs_n] alternative to assuming that every recursive
   call returns.  For a requested bound [S n], consume edge signals up to
   the next materialized column word.  Crossing that word either already
   supplies the requested finite prefix, or returns to the smaller request
   [n] at the next dotted-edge phase. *)
Lemma dynamic_side_unbounded tm P L top:
  (forall L0 top0, P L0 top0 -> dynamic_side_step tm P L0 top0) ->
  P L top ->
  quadRect tm L top.
Proof.
  intros Hstep HP.
  unfold quadRect, InfiniteRectInternal.quadRect.
  assert (Hn : forall n L0 top0, P L0 top0 ->
      @InfiniteRectInternal.sideS_n tm L0 top0 n).
  {
    induction n as [|n IH]; intros L0 top0 HP0.
    - apply InfiniteRectInternal.sideS_n_0.
    - destruct (Hstep _ _ HP0) as
        (hs & Ltail & Ledge & top' & w & width &
         Hwidth & Hw & HL & Hedge & Hrect & HP').
      specialize (IH _ _ HP').
      unfold downRect, InfiniteRectInternal.downRect in Hrect.
      specialize (Hrect top' n IH).
      eapply InfiniteRectInternal.sideS_n_mono.
      + rewrite HL.
        eapply InfiniteRectInternal.sideS_n_app_right;
          [exact Hedge|exact Hrect].
      + lia.
  }
  intros n; eapply Hn; eauto.
Qed.

(* Peel one finite dotted-column call in front of an already established
   right rectangle.  The dotted column consumes [hs] until it first emits
   the nonempty materialized word [w]; [downRect] moves that word through
   the intervening ordinary columns, leaving the next dotted column at
   [top'].  The target need not be presented through a closed phase
   predicate, so this lemma can be iterated over the acyclic initialization
   prefix. *)
Lemma sideRLs_downRect_quadRect tm
    (hs:list (DH0*DH0))
    (Ltail Ledge:Stream (DH0*DH0))
    (top top':side) (w:list Sym) (width:nat):
  0 < width ->
  sideRLs tm hs top (w *> top') ->
  downRect tm Ltail Ledge w width ->
  quadRect tm Ledge top' ->
  quadRect tm (hs *> Ltail) top.
Proof.
  intros Hwidth Hedge Hrect Hnext.
  assert (Hword:quadRect tm Ltail (w *> top')).
  { eapply downRect_quadRect_concat; eauto. }
  unfold quadRect, InfiniteRectInternal.quadRect in *.
  intro n.
  eapply InfiniteRectInternal.sideS_n_app_right;
    [exact Hedge|exact (Hword n)].
Qed.

Definition tm := Eval compute in (TM_from_str "1RB0RD_0RC---_1LD0RC_1RE0LE_1RF1LE_0LD1RA").

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6);
    [vm_compute; reflexivity | st; reflexivity]).

(* Directed heads and stationary column words from TM4y1.txt. *)
Notation hashR := (C,<[0]).
Notation hashL := (E,[1]).
Notation atSignalR := (C,<[0;0;0]).
Notation atSignalL := (E,[1;1;1;1;0;0;1;1]).
Notation dollarR := (D,<[1;1;0]).
Notation dollarL := (E,[1;1;0;0;1;1;0;0]).
Notation hash := [(hashR,hashL)].
Notation atSignal := [(atSignalR,atSignalL)].
Notation dollar := [(dollarR,dollarL)].

Notation cellX := [1;1;1;0;0;1;1].
Notation cellY := [1;1;1;0;0;0;0].
Notation cellH := [1;0].
Notation cellD := [1;0;0;1;1;0;0].
Notation cellP := [1;1].
Notation cellQ := [0;0].


(* Positive-width forms for the ordinary-column [downRect] construction. *)
Lemma hash_X_n: segRLs_n tm hash hash cellX cellX 1.
Proof. solve_segRLs_n1. Qed.
Lemma hash_Y_n: segRLs_n tm hash hash cellY cellY 1.
Proof. solve_segRLs_n1. Qed.
Lemma at_X_n: segRLs_n tm atSignal (hash++atSignal) cellX cellX 1.
Proof. solve_segRLs_n1. Qed.
Lemma at_Y_n: segRLs_n tm atSignal hash cellY cellH 1.
Proof. solve_segRLs_n1. Qed.
Lemma hash_H_n: segRLs_n tm hash dollar cellH cellD 1.
Proof. solve_segRLs_n1. Qed.
Lemma hash_D_n: segRLs_n tm hash [] cellD cellY 1.
Proof. solve_segRLs_n1. Qed.
Lemma dollar_X_n: segRLs_n tm dollar [] cellX cellP 1.
Proof. solve_segRLs_n1. Qed.
Lemma dollar_Y_n: segRLs_n tm dollar [] cellY cellQ 1.
Proof. solve_segRLs_n1. Qed.
Lemma hash_P_n: segRLs_n tm hash atSignal cellP cellX 1.
Proof. solve_segRLs_n1. Qed.

Lemma hashes_X_n (k:nat):
  k <> O ->
  segRLs_n tm (hash^^k) (hash^^k) cellX cellX 1.
Proof.
  intro Hk. apply segRLs_n_wall; [exact hash_X_n|exact Hk].
Qed.

Lemma hashes_at_X_n (k:nat):
  segRLs_n tm ((hash^^k)++atSignal) ((hash^^(S k))++atSignal)
    cellX cellX 1.
Proof.
  destruct k as [|k].
  - cbn [lpow]. exact at_X_n.
  - replace ((hash^^(S (S k)))++atSignal)
      with ((hash^^(S k))++(hash++atSignal)).
    + eapply segRLs_n_trans.
      * apply hashes_X_n; lia.
      * exact at_X_n.
      * lia.
      * reflexivity.
    + rewrite (lpow_S_right hash (S k)), app_assoc. reflexivity.
Qed.

Definition at_packets (k:nat) : Stream (DH0*DH0) :=
  growing_packets (hashR,hashL) (atSignalR,atSignalL) k.

Definition dollar_packets (k:nat) : Stream (DH0*DH0) :=
  growing_packets (hashR,hashL) (dollarR,dollarL) k.

Lemma X_at_packets_downRect (k:nat):
  downRect tm (at_packets k) (at_packets (S k)) cellX 1.
Proof.
  eapply segRLs_n_inf_trans with
    (P:=fun L R top => exists j:nat,
      L = at_packets j /\
      R = at_packets (S j) /\ top = cellX).
  - intros L R top [j [HL [HR Htop]]]. subst L R top.
    exists ((hash^^j)++atSignal), ((hash^^(S j))++atSignal),
      cellX, (at_packets (S j)), (at_packets (S (S j))).
    split.
    + rewrite length_app. cbn. lia.
    + split.
      * unfold at_packets. rewrite growing_packets_unfold.
        rewrite repeat_singleton_lpow. reflexivity.
      * split.
        -- unfold at_packets at 1. rewrite growing_packets_unfold.
           rewrite repeat_singleton_lpow. reflexivity.
        -- split.
           ++ apply hashes_at_X_n.
           ++ exists (S j). repeat split; reflexivity.
  - exists k. repeat split; reflexivity.
Qed.

Lemma hashes_at_Y_H_n (k:nat):
  segRLs_n tm ((hash^^k)++atSignal) (hash^^(S k)) cellY cellH 1.
Proof.
  destruct k as [|k].
  - cbn [lpow]. exact at_Y_n.
  - rewrite (lpow_S_right hash (S k)).
    eapply segRLs_n_trans.
    + apply segRLs_n_wall; [exact hash_Y_n|lia].
    + exact at_Y_n.
    + lia.
    + lia.
Qed.

Lemma hash_hash_H_Y_n:
  segRLs_n tm (hash++hash) dollar cellH cellY 1.
Proof.
  change (segRLs_n tm (hash++hash) (dollar++[])
    cellH cellY 1).
  eapply segRLs_n_trans.
  - exact hash_H_n.
  - exact hash_D_n.
  - lia.
  - lia.
Qed.

Lemma hashes_at_H_n (n:nat):
  segRLs_n tm ((hash^^(S (S n)))++atSignal)
    (dollar++(hash^^(S n))) cellH cellH 1.
Proof.
  replace ((hash^^(S (S n)))++atSignal)
    with ((hash++hash)++((hash^^n)++atSignal)).
  - eapply segRLs_n_trans.
    + exact hash_hash_H_Y_n.
    + exact (hashes_at_Y_H_n n).
    + lia.
    + lia.
  - repeat rewrite lpow_S. repeat rewrite app_assoc. reflexivity.
Qed.

Lemma H_at_packets_downRect (n:nat):
  downRect tm (at_packets (S (S n)))
    (dollar *> dollar_packets (S n)) cellH 1.
Proof.
  eapply segRLs_n_inf_trans with
    (P:=fun L R top => exists j:nat,
      L = at_packets (S (S j)) /\
      R = dollar *> dollar_packets (S j) /\ top = cellH).
  - intros L R top [j [HL [HR Htop]]]. subst L R top.
    exists ((hash^^(S (S j)))++atSignal),
      (dollar++(hash^^(S j))), cellH,
      (at_packets (S (S (S j)))),
      (dollar *> dollar_packets (S (S j))).
    split.
    + rewrite length_app. cbn. lia.
    + split.
      * unfold at_packets. rewrite growing_packets_unfold.
        rewrite repeat_singleton_lpow. reflexivity.
      * split.
        -- unfold dollar_packets at 1.
           rewrite growing_packets_unfold, repeat_singleton_lpow.
           repeat rewrite Str_app_assoc. reflexivity.
        -- split.
           ++ apply hashes_at_H_n.
           ++ exists (S j). repeat split; reflexivity.
  - exists n. repeat split; reflexivity.
Qed.

Lemma hashes_dollar_X_P_n (n:nat):
  segRLs_n tm ((hash^^n)++dollar) (hash^^n) cellX cellP 1.
Proof.
  destruct n as [|n].
  - cbn [lpow]. exact dollar_X_n.
  - assert (Hseg: segRLs_n tm ((hash^^(S n))++dollar)
      ((hash^^(S n))++[]) cellX cellP 1).
    { eapply segRLs_n_trans.
      - apply segRLs_n_wall; [exact hash_X_n|lia].
      - exact dollar_X_n.
      - lia.
      - lia. }
    rewrite app_nil_r in Hseg. exact Hseg.
Qed.

Lemma hashes_dollar_P_n (n:nat):
  segRLs_n tm ((hash^^(S n))++dollar)
    (atSignal++(hash^^n)) cellP cellP 1.
Proof.
  rewrite lpow_S.
  change (segRLs_n tm (hash++((hash^^n)++dollar))
    (atSignal++(hash^^n)) cellP cellP 1).
  eapply segRLs_n_trans.
  - exact hash_P_n.
  - exact (hashes_dollar_X_P_n n).
  - lia.
  - lia.
Qed.

Lemma P_dollar_packets_downRect (n:nat):
  downRect tm (dollar_packets (S n))
    (atSignal *> at_packets n) cellP 1.
Proof.
  eapply segRLs_n_inf_trans with
    (P:=fun L R top => exists j:nat,
      L = dollar_packets (S j) /\
      R = atSignal *> at_packets j /\ top = cellP).
  - intros L R top [j [HL [HR Htop]]]. subst L R top.
    exists ((hash^^(S j))++dollar),
      (atSignal++(hash^^j)), cellP,
      (dollar_packets (S (S j))),
      (atSignal *> at_packets (S j)).
    split.
    + rewrite length_app. cbn. lia.
    + split.
      * unfold dollar_packets. rewrite growing_packets_unfold.
        rewrite repeat_singleton_lpow. reflexivity.
      * split.
        -- unfold at_packets at 1.
           rewrite growing_packets_unfold, repeat_singleton_lpow.
           repeat rewrite Str_app_assoc. reflexivity.
        -- split.
           ++ apply hashes_dollar_P_n.
           ++ exists (S j). repeat split; reflexivity.
  - exists n. repeat split; reflexivity.
Qed.

Lemma hash3_Q_Y_n:
  segRLs_n tm (hash++hash++hash) dollar cellQ cellY 1.
Proof. solve_segRLs_n1. Qed.

Lemma hashes_dollar_Y_Q_n (n:nat):
  segRLs_n tm ((hash^^n)++dollar) (hash^^n) cellY cellQ 1.
Proof.
  destruct n as [|n].
  - cbn [lpow]. exact dollar_Y_n.
  - assert (Hseg: segRLs_n tm ((hash^^(S n))++dollar)
      ((hash^^(S n))++[]) cellY cellQ 1).
    { eapply segRLs_n_trans.
      - apply segRLs_n_wall; [exact hash_Y_n|lia].
      - exact dollar_Y_n.
      - lia.
      - lia. }
    rewrite app_nil_r in Hseg. exact Hseg.
Qed.

Lemma hashes_dollar_Q_n (n:nat):
  segRLs_n tm ((hash^^(S (S (S n))))++dollar)
    (dollar++(hash^^n)) cellQ cellQ 1.
Proof.
  replace ((hash^^(S (S (S n))))++dollar)
    with ((hash++hash++hash)++((hash^^n)++dollar)).
  - eapply segRLs_n_trans.
    + exact hash3_Q_Y_n.
    + exact (hashes_dollar_Y_Q_n n).
    + lia.
    + lia.
  - repeat rewrite lpow_S. repeat rewrite app_assoc. reflexivity.
Qed.

Lemma Q_dollar_packets_downRect (n:nat):
  downRect tm (dollar_packets (S (S (S n))))
    (dollar *> dollar_packets n) cellQ 1.
Proof.
  eapply segRLs_n_inf_trans with
    (P:=fun L R top => exists j:nat,
      L = dollar_packets (S (S (S j))) /\
      R = dollar *> dollar_packets j /\ top = cellQ).
  - intros L R top [j [HL [HR Htop]]]. subst L R top.
    exists ((hash^^(S (S (S j))))++dollar),
      (dollar++(hash^^j)), cellQ,
      (dollar_packets (S (S (S (S j))))),
      (dollar *> dollar_packets (S j)).
    split.
    + rewrite length_app. cbn. lia.
    + split.
      * unfold dollar_packets. rewrite growing_packets_unfold.
        rewrite repeat_singleton_lpow. reflexivity.
      * split.
        -- unfold dollar_packets at 1.
           rewrite growing_packets_unfold, repeat_singleton_lpow.
           repeat rewrite Str_app_assoc. reflexivity.
        -- split.
           ++ apply hashes_dollar_Q_n.
           ++ exists (S j). repeat split; reflexivity.
  - exists n. repeat split; reflexivity.
Qed.

Lemma X_dollar_column_downRect (a n:nat):
  downRect tm
    ((hash^^a) *> dollar *> dollar_packets (S n))
    ((hash^^a) *> atSignal *> at_packets n) cellX 1.
Proof.
  rewrite <- Str_app_assoc.
  eapply segRLs_n_downRect_trans.
  - apply hashes_dollar_X_P_n.
  - apply P_dollar_packets_downRect.
Qed.

Lemma X_dollar_column_downRect_normalized (a:nat):
  downRect tm
    ((hash^^a) *> dollar *> dollar_packets (S (S a)))
    (at_packets a) cellX 1.
Proof.
  unfold at_packets at 1.
  rewrite growing_packets_unfold, repeat_singleton_lpow, Str_app_assoc.
  exact (X_dollar_column_downRect a (S a)).
Qed.

Lemma X_at_column_downRect (a k:nat):
  downRect tm
    ((hash^^a) *> atSignal *> at_packets k)
    ((hash^^(S a)) *> atSignal *> at_packets (S k)) cellX 1.
Proof.
  do 2 rewrite <- Str_app_assoc.
  eapply segRLs_n_downRect_trans.
  - apply hashes_at_X_n.
  - apply X_at_packets_downRect.
Qed.

Lemma Y_at_column_downRect (a n:nat):
  downRect tm
    ((hash^^a) *> atSignal *> at_packets (S (S n)))
    ((hash^^(S a)) *> dollar *>
      dollar_packets (S n)) cellY 1.
Proof.
  rewrite <- Str_app_assoc.
  eapply segRLs_n_downRect_trans.
  - apply hashes_at_Y_H_n.
  - apply H_at_packets_downRect.
Qed.

Lemma Y_at_column_downRect_normalized (a:nat):
  downRect tm
    ((hash^^a) *> atSignal *> at_packets (S (S (S a))))
    (dollar_packets (S a)) cellY 1.
Proof.
  unfold dollar_packets at 1.
  rewrite growing_packets_unfold, repeat_singleton_lpow, Str_app_assoc.
  exact (Y_at_column_downRect a (S a)).
Qed.

Lemma Y_dollar_column_downRect (a n:nat):
  downRect tm
    ((hash^^a) *> dollar *>
      dollar_packets (S (S (S n))))
    ((hash^^a) *> dollar *> dollar_packets n) cellY 1.
Proof.
  rewrite <- Str_app_assoc.
  eapply segRLs_n_downRect_trans.
  - apply hashes_dollar_Y_Q_n.
  - apply Q_dollar_packets_downRect.
Qed.

Lemma dollar_packet_normalize (r m:nat):
  (hash^^(r+m)) *> dollar *> dollar_packets (S m) =
  (hash^^r) *> dollar_packets m.
Proof.
  unfold dollar_packets at 2.
  rewrite growing_packets_unfold, repeat_singleton_lpow.
  rewrite lpow_add. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma Y_dollar_column_downRect_normalized (r m:nat):
  downRect tm
    ((hash^^(r+m)) *> dollar *>
      dollar_packets (S (S (S (S m)))))
    ((hash^^r) *> dollar_packets m) cellY 1.
Proof.
  rewrite <- dollar_packet_normalize.
  apply Y_dollar_column_downRect.
Qed.

(* Transient ordinary columns occurring only in the finite initialization. *)

Lemma D_at_column_downRect (m:nat):
  downRect tm
    ((hash^^(S m)) *> atSignal *>
      at_packets (S (S (S m))))
    (dollar_packets (S m)) cellD 1.
Proof.
  rewrite lpow_S, Str_app_assoc.
  unfold dollar_packets at 1.
  rewrite growing_packets_unfold, repeat_singleton_lpow.
  rewrite Str_app_assoc.
  eapply segRLs_n_downRect_trans with (hL:=hash) (hR:=[]).
  - exact hash_D_n.
  - pose proof (Y_at_column_downRect m (S m)) as H.
    rewrite lpow_S, Str_app_assoc in H; exact H.
Qed.


(* The 189 emission phases use only these 18 distinct grouped dotted-edge
   rules; their different phases are carried by the stream descriptor, not
   by duplicating the same [sideRLs] proof. *)
Definition y_edge_group_rules : list edge_group_text := [
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "###@#####" "Y" "1110011101";
  mk_edge_group_text "1110011101" "#####" "X" "11100111011";
  mk_edge_group_text "11100001" "##@#####" "XXXX" "11100001";
  mk_edge_group_text "11100111011" "##$########" "X"
    "1110011101001111110011101";
  mk_edge_group_text "1110011101001111110011101" "#####" "X"
    "111001110100001100001";
  mk_edge_group_text "111001110100001100001" "###" "XX"
    "11100111001111";
  mk_edge_group_text "11100111001111" "#" "X" "1110011";
  mk_edge_group_text "1110011" "#####" "X" "11100111011";
  mk_edge_group_text "111001110101111" "@#####" "X" "11100111011";
  mk_edge_group_text "11100001" "#@#######" "X" "1110011101";
  mk_edge_group_text "111001110101111" "#@##" "X" "11100111";
  mk_edge_group_text "11100111" "####" "X" "11100111011";
  mk_edge_group_text "11100111011" "####$##" "X"
    "111001100100001";
  mk_edge_group_text "111001100100001" "####" "X" "1110011101";
  mk_edge_group_text "11100111011" "#$##" "Y" "11100001"
].

Definition y_edge_group_sound :=
  edge_group_sound tm hash atSignal dollar cellX cellY.


Lemma y_edge_group_rules_sound:
  Forall y_edge_group_sound y_edge_group_rules.
Proof.
  unfold y_edge_group_rules.
  repeat (apply Forall_cons; [
    unfold y_edge_group_sound,edge_group_sound;
    cbn [signal_word_of_string bit_word_of_string column_word_of_string];
    esc|]).
  apply Forall_nil.
Qed.

Definition y_edge_phases : list edge_phase_text := [
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#" PacketDollar 39) (mk_packet_stream_text "####################################$" PacketDollar 40) (mk_packet_stream_text "" PacketDollar 36);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "" PacketDollar 36) (mk_packet_stream_text "###############################$" PacketDollar 37) (mk_packet_stream_text "###############################@" PacketAt 36);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###############################@" PacketAt 36) (mk_packet_stream_text "#############################@" PacketAt 36) (mk_packet_stream_text "##############################@" PacketAt 37);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##############################@" PacketAt 37) (mk_packet_stream_text "##########################@" PacketAt 37) (mk_packet_stream_text "###########################$" PacketDollar 36);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###########################$" PacketDollar 36) (mk_packet_stream_text "######################$" PacketDollar 36) (mk_packet_stream_text "######################@" PacketAt 35);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "######################@" PacketAt 35) (mk_packet_stream_text "####################@" PacketAt 35) (mk_packet_stream_text "#####################@" PacketAt 36);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#####################@" PacketAt 36) (mk_packet_stream_text "#################@" PacketAt 36) (mk_packet_stream_text "##################$" PacketDollar 35);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "##################$" PacketDollar 35) (mk_packet_stream_text "#############$" PacketDollar 35) (mk_packet_stream_text "#############@" PacketAt 34);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#############@" PacketAt 34) (mk_packet_stream_text "###########@" PacketAt 34) (mk_packet_stream_text "############@" PacketAt 35);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "############@" PacketAt 35) (mk_packet_stream_text "########@" PacketAt 35) (mk_packet_stream_text "#########$" PacketDollar 34);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#########$" PacketDollar 34) (mk_packet_stream_text "####$" PacketDollar 34) (mk_packet_stream_text "####@" PacketAt 33);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "####@" PacketAt 33) (mk_packet_stream_text "##@" PacketAt 33) (mk_packet_stream_text "###@" PacketAt 34);
  mk_edge_phase_text (mk_edge_group_text "11100001" "###@#####" "Y" "1110011101") (mk_packet_stream_text "###@" PacketAt 34) (mk_packet_stream_text "#############################@" PacketAt 35) (mk_packet_stream_text "##############################$" PacketDollar 34);
  mk_edge_phase_text (mk_edge_group_text "1110011101" "#####" "X" "11100111011") (mk_packet_stream_text "##############################$" PacketDollar 34) (mk_packet_stream_text "#########################$" PacketDollar 34) (mk_packet_stream_text "#########################@" PacketAt 33);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#########################@" PacketAt 33) (mk_packet_stream_text "####################@" PacketAt 33) (mk_packet_stream_text "#####################@" PacketAt 34);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#####################@" PacketAt 34) (mk_packet_stream_text "###################@" PacketAt 34) (mk_packet_stream_text "####################@" PacketAt 35);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "####################@" PacketAt 35) (mk_packet_stream_text "################@" PacketAt 35) (mk_packet_stream_text "#################$" PacketDollar 34);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#################$" PacketDollar 34) (mk_packet_stream_text "############$" PacketDollar 34) (mk_packet_stream_text "############@" PacketAt 33);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "############@" PacketAt 33) (mk_packet_stream_text "##########@" PacketAt 33) (mk_packet_stream_text "###########@" PacketAt 34);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "###########@" PacketAt 34) (mk_packet_stream_text "#######@" PacketAt 34) (mk_packet_stream_text "########$" PacketDollar 33);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "########$" PacketDollar 33) (mk_packet_stream_text "###$" PacketDollar 33) (mk_packet_stream_text "###@" PacketAt 32);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###@" PacketAt 32) (mk_packet_stream_text "#@" PacketAt 32) (mk_packet_stream_text "##@" PacketAt 33);
  mk_edge_phase_text (mk_edge_group_text "11100001" "##@#####" "XXXX" "11100001") (mk_packet_stream_text "##@" PacketAt 33) (mk_packet_stream_text "############################@" PacketAt 34) (mk_packet_stream_text "################################@" PacketAt 38);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "################################@" PacketAt 38) (mk_packet_stream_text "############################@" PacketAt 38) (mk_packet_stream_text "#############################$" PacketDollar 37);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#############################$" PacketDollar 37) (mk_packet_stream_text "########################$" PacketDollar 37) (mk_packet_stream_text "########################@" PacketAt 36);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "########################@" PacketAt 36) (mk_packet_stream_text "######################@" PacketAt 36) (mk_packet_stream_text "#######################@" PacketAt 37);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#######################@" PacketAt 37) (mk_packet_stream_text "###################@" PacketAt 37) (mk_packet_stream_text "####################$" PacketDollar 36);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "####################$" PacketDollar 36) (mk_packet_stream_text "###############$" PacketDollar 36) (mk_packet_stream_text "###############@" PacketAt 35);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###############@" PacketAt 35) (mk_packet_stream_text "#############@" PacketAt 35) (mk_packet_stream_text "##############@" PacketAt 36);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##############@" PacketAt 36) (mk_packet_stream_text "##########@" PacketAt 36) (mk_packet_stream_text "###########$" PacketDollar 35);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###########$" PacketDollar 35) (mk_packet_stream_text "######$" PacketDollar 35) (mk_packet_stream_text "######@" PacketAt 34);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "######@" PacketAt 34) (mk_packet_stream_text "####@" PacketAt 34) (mk_packet_stream_text "#####@" PacketAt 35);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#####@" PacketAt 35) (mk_packet_stream_text "#@" PacketAt 35) (mk_packet_stream_text "##$" PacketDollar 34);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "##$########" "X" "1110011101001111110011101") (mk_packet_stream_text "##$" PacketDollar 34) (mk_packet_stream_text "##########################$" PacketDollar 35) (mk_packet_stream_text "##########################@" PacketAt 34);
  mk_edge_phase_text (mk_edge_group_text "1110011101001111110011101" "#####" "X" "111001110100001100001") (mk_packet_stream_text "##########################@" PacketAt 34) (mk_packet_stream_text "#####################@" PacketAt 34) (mk_packet_stream_text "######################@" PacketAt 35);
  mk_edge_phase_text (mk_edge_group_text "111001110100001100001" "###" "XX" "11100111001111") (mk_packet_stream_text "######################@" PacketAt 35) (mk_packet_stream_text "###################@" PacketAt 35) (mk_packet_stream_text "#####################@" PacketAt 37);
  mk_edge_phase_text (mk_edge_group_text "11100111001111" "#" "X" "1110011") (mk_packet_stream_text "#####################@" PacketAt 37) (mk_packet_stream_text "####################@" PacketAt 37) (mk_packet_stream_text "#####################@" PacketAt 38);
  mk_edge_phase_text (mk_edge_group_text "1110011" "#####" "X" "11100111011") (mk_packet_stream_text "#####################@" PacketAt 38) (mk_packet_stream_text "################@" PacketAt 38) (mk_packet_stream_text "#################@" PacketAt 39);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#################@" PacketAt 39) (mk_packet_stream_text "############@" PacketAt 39) (mk_packet_stream_text "#############@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#############@" PacketAt 40) (mk_packet_stream_text "###########@" PacketAt 40) (mk_packet_stream_text "############@" PacketAt 41);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "############@" PacketAt 41) (mk_packet_stream_text "########@" PacketAt 41) (mk_packet_stream_text "#########$" PacketDollar 40);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#########$" PacketDollar 40) (mk_packet_stream_text "####$" PacketDollar 40) (mk_packet_stream_text "####@" PacketAt 39);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "####@" PacketAt 39) (mk_packet_stream_text "##@" PacketAt 39) (mk_packet_stream_text "###@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "11100001" "###@#####" "Y" "1110011101") (mk_packet_stream_text "###@" PacketAt 40) (mk_packet_stream_text "###################################@" PacketAt 41) (mk_packet_stream_text "####################################$" PacketDollar 40);
  mk_edge_phase_text (mk_edge_group_text "1110011101" "#####" "X" "11100111011") (mk_packet_stream_text "####################################$" PacketDollar 40) (mk_packet_stream_text "###############################$" PacketDollar 40) (mk_packet_stream_text "###############################@" PacketAt 39);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###############################@" PacketAt 39) (mk_packet_stream_text "##########################@" PacketAt 39) (mk_packet_stream_text "###########################@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###########################@" PacketAt 40) (mk_packet_stream_text "#########################@" PacketAt 40) (mk_packet_stream_text "##########################@" PacketAt 41);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##########################@" PacketAt 41) (mk_packet_stream_text "######################@" PacketAt 41) (mk_packet_stream_text "#######################$" PacketDollar 40);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#######################$" PacketDollar 40) (mk_packet_stream_text "##################$" PacketDollar 40) (mk_packet_stream_text "##################@" PacketAt 39);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##################@" PacketAt 39) (mk_packet_stream_text "################@" PacketAt 39) (mk_packet_stream_text "#################@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#################@" PacketAt 40) (mk_packet_stream_text "#############@" PacketAt 40) (mk_packet_stream_text "##############$" PacketDollar 39);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "##############$" PacketDollar 39) (mk_packet_stream_text "#########$" PacketDollar 39) (mk_packet_stream_text "#########@" PacketAt 38);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#########@" PacketAt 38) (mk_packet_stream_text "#######@" PacketAt 38) (mk_packet_stream_text "########@" PacketAt 39);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "########@" PacketAt 39) (mk_packet_stream_text "####@" PacketAt 39) (mk_packet_stream_text "#####$" PacketDollar 38);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#####$" PacketDollar 38) (mk_packet_stream_text "$" PacketDollar 38) (mk_packet_stream_text "@" PacketAt 37);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "@#####" "X" "11100111011") (mk_packet_stream_text "@" PacketAt 37) (mk_packet_stream_text "################################@" PacketAt 38) (mk_packet_stream_text "#################################@" PacketAt 39);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#################################@" PacketAt 39) (mk_packet_stream_text "############################@" PacketAt 39) (mk_packet_stream_text "#############################@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#############################@" PacketAt 40) (mk_packet_stream_text "###########################@" PacketAt 40) (mk_packet_stream_text "############################@" PacketAt 41);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "############################@" PacketAt 41) (mk_packet_stream_text "########################@" PacketAt 41) (mk_packet_stream_text "#########################$" PacketDollar 40);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#########################$" PacketDollar 40) (mk_packet_stream_text "####################$" PacketDollar 40) (mk_packet_stream_text "####################@" PacketAt 39);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "####################@" PacketAt 39) (mk_packet_stream_text "##################@" PacketAt 39) (mk_packet_stream_text "###################@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "###################@" PacketAt 40) (mk_packet_stream_text "###############@" PacketAt 40) (mk_packet_stream_text "################$" PacketDollar 39);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "################$" PacketDollar 39) (mk_packet_stream_text "###########$" PacketDollar 39) (mk_packet_stream_text "###########@" PacketAt 38);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###########@" PacketAt 38) (mk_packet_stream_text "#########@" PacketAt 38) (mk_packet_stream_text "##########@" PacketAt 39);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##########@" PacketAt 39) (mk_packet_stream_text "######@" PacketAt 39) (mk_packet_stream_text "#######$" PacketDollar 38);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#######$" PacketDollar 38) (mk_packet_stream_text "##$" PacketDollar 38) (mk_packet_stream_text "##@" PacketAt 37);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##@" PacketAt 37) (mk_packet_stream_text "@" PacketAt 37) (mk_packet_stream_text "#@" PacketAt 38);
  mk_edge_phase_text (mk_edge_group_text "11100001" "#@#######" "X" "1110011101") (mk_packet_stream_text "#@" PacketAt 38) (mk_packet_stream_text "###############################@" PacketAt 39) (mk_packet_stream_text "################################@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "1110011101" "#####" "X" "11100111011") (mk_packet_stream_text "################################@" PacketAt 40) (mk_packet_stream_text "###########################@" PacketAt 40) (mk_packet_stream_text "############################@" PacketAt 41);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "############################@" PacketAt 41) (mk_packet_stream_text "#######################@" PacketAt 41) (mk_packet_stream_text "########################@" PacketAt 42);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "########################@" PacketAt 42) (mk_packet_stream_text "######################@" PacketAt 42) (mk_packet_stream_text "#######################@" PacketAt 43);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#######################@" PacketAt 43) (mk_packet_stream_text "###################@" PacketAt 43) (mk_packet_stream_text "####################$" PacketDollar 42);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "####################$" PacketDollar 42) (mk_packet_stream_text "###############$" PacketDollar 42) (mk_packet_stream_text "###############@" PacketAt 41);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###############@" PacketAt 41) (mk_packet_stream_text "#############@" PacketAt 41) (mk_packet_stream_text "##############@" PacketAt 42);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##############@" PacketAt 42) (mk_packet_stream_text "##########@" PacketAt 42) (mk_packet_stream_text "###########$" PacketDollar 41);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###########$" PacketDollar 41) (mk_packet_stream_text "######$" PacketDollar 41) (mk_packet_stream_text "######@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "######@" PacketAt 40) (mk_packet_stream_text "####@" PacketAt 40) (mk_packet_stream_text "#####@" PacketAt 41);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#####@" PacketAt 41) (mk_packet_stream_text "#@" PacketAt 41) (mk_packet_stream_text "##$" PacketDollar 40);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "##$########" "X" "1110011101001111110011101") (mk_packet_stream_text "##$" PacketDollar 40) (mk_packet_stream_text "################################$" PacketDollar 41) (mk_packet_stream_text "################################@" PacketAt 40);
  mk_edge_phase_text (mk_edge_group_text "1110011101001111110011101" "#####" "X" "111001110100001100001") (mk_packet_stream_text "################################@" PacketAt 40) (mk_packet_stream_text "###########################@" PacketAt 40) (mk_packet_stream_text "############################@" PacketAt 41);
  mk_edge_phase_text (mk_edge_group_text "111001110100001100001" "###" "XX" "11100111001111") (mk_packet_stream_text "############################@" PacketAt 41) (mk_packet_stream_text "#########################@" PacketAt 41) (mk_packet_stream_text "###########################@" PacketAt 43);
  mk_edge_phase_text (mk_edge_group_text "11100111001111" "#" "X" "1110011") (mk_packet_stream_text "###########################@" PacketAt 43) (mk_packet_stream_text "##########################@" PacketAt 43) (mk_packet_stream_text "###########################@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "1110011" "#####" "X" "11100111011") (mk_packet_stream_text "###########################@" PacketAt 44) (mk_packet_stream_text "######################@" PacketAt 44) (mk_packet_stream_text "#######################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#######################@" PacketAt 45) (mk_packet_stream_text "##################@" PacketAt 45) (mk_packet_stream_text "###################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###################@" PacketAt 46) (mk_packet_stream_text "#################@" PacketAt 46) (mk_packet_stream_text "##################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##################@" PacketAt 47) (mk_packet_stream_text "##############@" PacketAt 47) (mk_packet_stream_text "###############$" PacketDollar 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###############$" PacketDollar 46) (mk_packet_stream_text "##########$" PacketDollar 46) (mk_packet_stream_text "##########@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##########@" PacketAt 45) (mk_packet_stream_text "########@" PacketAt 45) (mk_packet_stream_text "#########@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#########@" PacketAt 46) (mk_packet_stream_text "#####@" PacketAt 46) (mk_packet_stream_text "######$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "######$" PacketDollar 45) (mk_packet_stream_text "#$" PacketDollar 45) (mk_packet_stream_text "#@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "#@##" "X" "11100111") (mk_packet_stream_text "#@" PacketAt 44) (mk_packet_stream_text "##########################################@" PacketAt 45) (mk_packet_stream_text "###########################################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100111" "####" "X" "11100111011") (mk_packet_stream_text "###########################################@" PacketAt 46) (mk_packet_stream_text "#######################################@" PacketAt 46) (mk_packet_stream_text "########################################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "########################################@" PacketAt 47) (mk_packet_stream_text "###################################@" PacketAt 47) (mk_packet_stream_text "####################################@" PacketAt 48);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "####################################@" PacketAt 48) (mk_packet_stream_text "##################################@" PacketAt 48) (mk_packet_stream_text "###################################@" PacketAt 49);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "###################################@" PacketAt 49) (mk_packet_stream_text "###############################@" PacketAt 49) (mk_packet_stream_text "################################$" PacketDollar 48);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "################################$" PacketDollar 48) (mk_packet_stream_text "###########################$" PacketDollar 48) (mk_packet_stream_text "###########################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###########################@" PacketAt 47) (mk_packet_stream_text "#########################@" PacketAt 47) (mk_packet_stream_text "##########################@" PacketAt 48);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##########################@" PacketAt 48) (mk_packet_stream_text "######################@" PacketAt 48) (mk_packet_stream_text "#######################$" PacketDollar 47);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#######################$" PacketDollar 47) (mk_packet_stream_text "##################$" PacketDollar 47) (mk_packet_stream_text "##################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##################@" PacketAt 46) (mk_packet_stream_text "################@" PacketAt 46) (mk_packet_stream_text "#################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#################@" PacketAt 47) (mk_packet_stream_text "#############@" PacketAt 47) (mk_packet_stream_text "##############$" PacketDollar 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "##############$" PacketDollar 46) (mk_packet_stream_text "#########$" PacketDollar 46) (mk_packet_stream_text "#########@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#########@" PacketAt 45) (mk_packet_stream_text "#######@" PacketAt 45) (mk_packet_stream_text "########@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "########@" PacketAt 46) (mk_packet_stream_text "####@" PacketAt 46) (mk_packet_stream_text "#####$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#####$" PacketDollar 45) (mk_packet_stream_text "$" PacketDollar 45) (mk_packet_stream_text "@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "@#####" "X" "11100111011") (mk_packet_stream_text "@" PacketAt 44) (mk_packet_stream_text "#######################################@" PacketAt 45) (mk_packet_stream_text "########################################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "########################################@" PacketAt 46) (mk_packet_stream_text "###################################@" PacketAt 46) (mk_packet_stream_text "####################################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "####################################@" PacketAt 47) (mk_packet_stream_text "##################################@" PacketAt 47) (mk_packet_stream_text "###################################@" PacketAt 48);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "###################################@" PacketAt 48) (mk_packet_stream_text "###############################@" PacketAt 48) (mk_packet_stream_text "################################$" PacketDollar 47);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "################################$" PacketDollar 47) (mk_packet_stream_text "###########################$" PacketDollar 47) (mk_packet_stream_text "###########################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###########################@" PacketAt 46) (mk_packet_stream_text "#########################@" PacketAt 46) (mk_packet_stream_text "##########################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##########################@" PacketAt 47) (mk_packet_stream_text "######################@" PacketAt 47) (mk_packet_stream_text "#######################$" PacketDollar 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#######################$" PacketDollar 46) (mk_packet_stream_text "##################$" PacketDollar 46) (mk_packet_stream_text "##################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##################@" PacketAt 45) (mk_packet_stream_text "################@" PacketAt 45) (mk_packet_stream_text "#################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#################@" PacketAt 46) (mk_packet_stream_text "#############@" PacketAt 46) (mk_packet_stream_text "##############$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "##############$" PacketDollar 45) (mk_packet_stream_text "#########$" PacketDollar 45) (mk_packet_stream_text "#########@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#########@" PacketAt 44) (mk_packet_stream_text "#######@" PacketAt 44) (mk_packet_stream_text "########@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "########@" PacketAt 45) (mk_packet_stream_text "####@" PacketAt 45) (mk_packet_stream_text "#####$" PacketDollar 44);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#####$" PacketDollar 44) (mk_packet_stream_text "$" PacketDollar 44) (mk_packet_stream_text "@" PacketAt 43);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "@#####" "X" "11100111011") (mk_packet_stream_text "@" PacketAt 43) (mk_packet_stream_text "######################################@" PacketAt 44) (mk_packet_stream_text "#######################################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#######################################@" PacketAt 45) (mk_packet_stream_text "##################################@" PacketAt 45) (mk_packet_stream_text "###################################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###################################@" PacketAt 46) (mk_packet_stream_text "#################################@" PacketAt 46) (mk_packet_stream_text "##################################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##################################@" PacketAt 47) (mk_packet_stream_text "##############################@" PacketAt 47) (mk_packet_stream_text "###############################$" PacketDollar 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###############################$" PacketDollar 46) (mk_packet_stream_text "##########################$" PacketDollar 46) (mk_packet_stream_text "##########################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##########################@" PacketAt 45) (mk_packet_stream_text "########################@" PacketAt 45) (mk_packet_stream_text "#########################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#########################@" PacketAt 46) (mk_packet_stream_text "#####################@" PacketAt 46) (mk_packet_stream_text "######################$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "######################$" PacketDollar 45) (mk_packet_stream_text "#################$" PacketDollar 45) (mk_packet_stream_text "#################@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#################@" PacketAt 44) (mk_packet_stream_text "###############@" PacketAt 44) (mk_packet_stream_text "################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "################@" PacketAt 45) (mk_packet_stream_text "############@" PacketAt 45) (mk_packet_stream_text "#############$" PacketDollar 44);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#############$" PacketDollar 44) (mk_packet_stream_text "########$" PacketDollar 44) (mk_packet_stream_text "########@" PacketAt 43);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "########@" PacketAt 43) (mk_packet_stream_text "######@" PacketAt 43) (mk_packet_stream_text "#######@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#######@" PacketAt 44) (mk_packet_stream_text "###@" PacketAt 44) (mk_packet_stream_text "####$" PacketDollar 43);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "####$##" "X" "111001100100001") (mk_packet_stream_text "####$" PacketDollar 43) (mk_packet_stream_text "#########################################$" PacketDollar 44) (mk_packet_stream_text "#########################################@" PacketAt 43);
  mk_edge_phase_text (mk_edge_group_text "111001100100001" "####" "X" "1110011101") (mk_packet_stream_text "#########################################@" PacketAt 43) (mk_packet_stream_text "#####################################@" PacketAt 43) (mk_packet_stream_text "######################################@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "1110011101" "#####" "X" "11100111011") (mk_packet_stream_text "######################################@" PacketAt 44) (mk_packet_stream_text "#################################@" PacketAt 44) (mk_packet_stream_text "##################################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "##################################@" PacketAt 45) (mk_packet_stream_text "#############################@" PacketAt 45) (mk_packet_stream_text "##############################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##############################@" PacketAt 46) (mk_packet_stream_text "############################@" PacketAt 46) (mk_packet_stream_text "#############################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#############################@" PacketAt 47) (mk_packet_stream_text "#########################@" PacketAt 47) (mk_packet_stream_text "##########################$" PacketDollar 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "##########################$" PacketDollar 46) (mk_packet_stream_text "#####################$" PacketDollar 46) (mk_packet_stream_text "#####################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#####################@" PacketAt 45) (mk_packet_stream_text "###################@" PacketAt 45) (mk_packet_stream_text "####################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "####################@" PacketAt 46) (mk_packet_stream_text "################@" PacketAt 46) (mk_packet_stream_text "#################$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#################$" PacketDollar 45) (mk_packet_stream_text "############$" PacketDollar 45) (mk_packet_stream_text "############@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "############@" PacketAt 44) (mk_packet_stream_text "##########@" PacketAt 44) (mk_packet_stream_text "###########@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "###########@" PacketAt 45) (mk_packet_stream_text "#######@" PacketAt 45) (mk_packet_stream_text "########$" PacketDollar 44);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "########$" PacketDollar 44) (mk_packet_stream_text "###$" PacketDollar 44) (mk_packet_stream_text "###@" PacketAt 43);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###@" PacketAt 43) (mk_packet_stream_text "#@" PacketAt 43) (mk_packet_stream_text "##@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "11100001" "##@#####" "XXXX" "11100001") (mk_packet_stream_text "##@" PacketAt 44) (mk_packet_stream_text "#######################################@" PacketAt 45) (mk_packet_stream_text "###########################################@" PacketAt 49);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "###########################################@" PacketAt 49) (mk_packet_stream_text "#######################################@" PacketAt 49) (mk_packet_stream_text "########################################$" PacketDollar 48);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "########################################$" PacketDollar 48) (mk_packet_stream_text "###################################$" PacketDollar 48) (mk_packet_stream_text "###################################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###################################@" PacketAt 47) (mk_packet_stream_text "#################################@" PacketAt 47) (mk_packet_stream_text "##################################@" PacketAt 48);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##################################@" PacketAt 48) (mk_packet_stream_text "##############################@" PacketAt 48) (mk_packet_stream_text "###############################$" PacketDollar 47);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###############################$" PacketDollar 47) (mk_packet_stream_text "##########################$" PacketDollar 47) (mk_packet_stream_text "##########################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##########################@" PacketAt 46) (mk_packet_stream_text "########################@" PacketAt 46) (mk_packet_stream_text "#########################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#########################@" PacketAt 47) (mk_packet_stream_text "#####################@" PacketAt 47) (mk_packet_stream_text "######################$" PacketDollar 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "######################$" PacketDollar 46) (mk_packet_stream_text "#################$" PacketDollar 46) (mk_packet_stream_text "#################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#################@" PacketAt 45) (mk_packet_stream_text "###############@" PacketAt 45) (mk_packet_stream_text "################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "################@" PacketAt 46) (mk_packet_stream_text "############@" PacketAt 46) (mk_packet_stream_text "#############$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#############$" PacketDollar 45) (mk_packet_stream_text "########$" PacketDollar 45) (mk_packet_stream_text "########@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "########@" PacketAt 44) (mk_packet_stream_text "######@" PacketAt 44) (mk_packet_stream_text "#######@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#######@" PacketAt 45) (mk_packet_stream_text "###@" PacketAt 45) (mk_packet_stream_text "####$" PacketDollar 44);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "####$##" "X" "111001100100001") (mk_packet_stream_text "####$" PacketDollar 44) (mk_packet_stream_text "##########################################$" PacketDollar 45) (mk_packet_stream_text "##########################################@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001100100001" "####" "X" "1110011101") (mk_packet_stream_text "##########################################@" PacketAt 44) (mk_packet_stream_text "######################################@" PacketAt 44) (mk_packet_stream_text "#######################################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "1110011101" "#####" "X" "11100111011") (mk_packet_stream_text "#######################################@" PacketAt 45) (mk_packet_stream_text "##################################@" PacketAt 45) (mk_packet_stream_text "###################################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###################################@" PacketAt 46) (mk_packet_stream_text "##############################@" PacketAt 46) (mk_packet_stream_text "###############################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "###############################@" PacketAt 47) (mk_packet_stream_text "#############################@" PacketAt 47) (mk_packet_stream_text "##############################@" PacketAt 48);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "##############################@" PacketAt 48) (mk_packet_stream_text "##########################@" PacketAt 48) (mk_packet_stream_text "###########################$" PacketDollar 47);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###########################$" PacketDollar 47) (mk_packet_stream_text "######################$" PacketDollar 47) (mk_packet_stream_text "######################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "######################@" PacketAt 46) (mk_packet_stream_text "####################@" PacketAt 46) (mk_packet_stream_text "#####################@" PacketAt 47);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#####################@" PacketAt 47) (mk_packet_stream_text "#################@" PacketAt 47) (mk_packet_stream_text "##################$" PacketDollar 46);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "##################$" PacketDollar 46) (mk_packet_stream_text "#############$" PacketDollar 46) (mk_packet_stream_text "#############@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#############@" PacketAt 45) (mk_packet_stream_text "###########@" PacketAt 45) (mk_packet_stream_text "############@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "############@" PacketAt 46) (mk_packet_stream_text "########@" PacketAt 46) (mk_packet_stream_text "#########$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "#########$" PacketDollar 45) (mk_packet_stream_text "####$" PacketDollar 45) (mk_packet_stream_text "####@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "####@" PacketAt 44) (mk_packet_stream_text "##@" PacketAt 44) (mk_packet_stream_text "###@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100001" "###@#####" "Y" "1110011101") (mk_packet_stream_text "###@" PacketAt 45) (mk_packet_stream_text "########################################@" PacketAt 46) (mk_packet_stream_text "#########################################$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "1110011101" "#####" "X" "11100111011") (mk_packet_stream_text "#########################################$" PacketDollar 45) (mk_packet_stream_text "####################################$" PacketDollar 45) (mk_packet_stream_text "####################################@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "####################################@" PacketAt 44) (mk_packet_stream_text "###############################@" PacketAt 44) (mk_packet_stream_text "################################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "################################@" PacketAt 45) (mk_packet_stream_text "##############################@" PacketAt 45) (mk_packet_stream_text "###############################@" PacketAt 46);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "###############################@" PacketAt 46) (mk_packet_stream_text "###########################@" PacketAt 46) (mk_packet_stream_text "############################$" PacketDollar 45);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "############################$" PacketDollar 45) (mk_packet_stream_text "#######################$" PacketDollar 45) (mk_packet_stream_text "#######################@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#######################@" PacketAt 44) (mk_packet_stream_text "#####################@" PacketAt 44) (mk_packet_stream_text "######################@" PacketAt 45);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "######################@" PacketAt 45) (mk_packet_stream_text "##################@" PacketAt 45) (mk_packet_stream_text "###################$" PacketDollar 44);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "###################$" PacketDollar 44) (mk_packet_stream_text "##############$" PacketDollar 44) (mk_packet_stream_text "##############@" PacketAt 43);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "##############@" PacketAt 43) (mk_packet_stream_text "############@" PacketAt 43) (mk_packet_stream_text "#############@" PacketAt 44);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "#############@" PacketAt 44) (mk_packet_stream_text "#########@" PacketAt 44) (mk_packet_stream_text "##########$" PacketDollar 43);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111") (mk_packet_stream_text "##########$" PacketDollar 43) (mk_packet_stream_text "#####$" PacketDollar 43) (mk_packet_stream_text "#####@" PacketAt 42);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001") (mk_packet_stream_text "#####@" PacketAt 42) (mk_packet_stream_text "###@" PacketAt 42) (mk_packet_stream_text "####@" PacketAt 43);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011") (mk_packet_stream_text "####@" PacketAt 43) (mk_packet_stream_text "@" PacketAt 43) (mk_packet_stream_text "#$" PacketDollar 42);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#$##" "Y" "11100001") (mk_packet_stream_text "#$" PacketDollar 42) (mk_packet_stream_text "########################################$" PacketDollar 43) (mk_packet_stream_text "#" PacketDollar 39)
].


Lemma y_Forall_split {A} (P:A->Prop) n xs:
  Forall P (firstn n xs) -> Forall P (skipn n xs) -> Forall P xs.
Proof.
  intros Hfirst Hrest; rewrite <- (firstn_skipn n xs).
  apply Forall_app; split; assumption.
Qed.

Lemma y_edge_phase_consumes_check_0:
  forallb edge_phase_consume_check
    (firstn 32 y_edge_phases) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_consumes_check_1:
  forallb edge_phase_consume_check
    (firstn 32 (skipn 32 y_edge_phases)) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_consumes_check_2:
  forallb edge_phase_consume_check
    (firstn 32 (skipn 32 (skipn 32 y_edge_phases))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_consumes_check_3:
  forallb edge_phase_consume_check
    (firstn 32
      (skipn 32 (skipn 32 (skipn 32 y_edge_phases)))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_consumes_check_4:
  forallb edge_phase_consume_check
    (firstn 32
      (skipn 32 (skipn 32 (skipn 32 (skipn 32
        y_edge_phases))))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_consumes_check_5:
  forallb edge_phase_consume_check
    (skipn 32 (skipn 32 (skipn 32 (skipn 32 (skipn 32
      y_edge_phases))))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_consumes:
  Forall (fun p =>
    packet_stream_text_consume
      (edge_group_consume (edge_phase_group p))
      (edge_phase_stream p) = Some (edge_phase_tail p))
    y_edge_phases.
Proof.
  eapply y_Forall_split with (n:=32).
  - eapply forallb_sound;
      [exact edge_phase_consume_check_sound|
       exact y_edge_phase_consumes_check_0].
  - eapply y_Forall_split with (n:=32).
    + eapply forallb_sound;
        [exact edge_phase_consume_check_sound|
         exact y_edge_phase_consumes_check_1].
    + eapply y_Forall_split with (n:=32).
      * eapply forallb_sound;
          [exact edge_phase_consume_check_sound|
           exact y_edge_phase_consumes_check_2].
      * eapply y_Forall_split with (n:=32).
        -- eapply forallb_sound;
             [exact edge_phase_consume_check_sound|
              exact y_edge_phase_consumes_check_3].
        -- eapply y_Forall_split with (n:=32).
           ++ eapply forallb_sound;
                [exact edge_phase_consume_check_sound|
                 exact y_edge_phase_consumes_check_4].
           ++ eapply forallb_sound;
                [exact edge_phase_consume_check_sound|
                 exact y_edge_phase_consumes_check_5].
Qed.

Definition y_edge_group_eq_dec (a b:edge_group_text) :
    {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

Definition y_edge_group_eqb (a b:edge_group_text) : bool :=
  if y_edge_group_eq_dec a b then true else false.

Lemma y_edge_group_eqb_eq a b:
  y_edge_group_eqb a b = true <-> a = b.
Proof.
  unfold y_edge_group_eqb.
  destruct (y_edge_group_eq_dec a b); split; congruence.
Qed.

Definition y_edge_phase_group_check (p:edge_phase_text) : bool :=
  existsb
    (y_edge_group_eqb (edge_phase_group p))
    y_edge_group_rules.

Lemma y_edge_phase_group_check_sound p:
  y_edge_phase_group_check p = true ->
  In (edge_phase_group p) y_edge_group_rules.
Proof.
  unfold y_edge_phase_group_check.
  rewrite existsb_exists.
  intros [g [Hg Heq]].
  apply y_edge_group_eqb_eq in Heq; subst; exact Hg.
Qed.

Lemma y_edge_phase_groups_check_0:
  forallb y_edge_phase_group_check
    (firstn 32 y_edge_phases) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_groups_check_1:
  forallb y_edge_phase_group_check
    (firstn 32 (skipn 32 y_edge_phases)) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_groups_check_2:
  forallb y_edge_phase_group_check
    (firstn 32 (skipn 32 (skipn 32 y_edge_phases))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_groups_check_3:
  forallb y_edge_phase_group_check
    (firstn 32
      (skipn 32 (skipn 32 (skipn 32 y_edge_phases)))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_groups_check_4:
  forallb y_edge_phase_group_check
    (firstn 32
      (skipn 32 (skipn 32 (skipn 32 (skipn 32
        y_edge_phases))))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_groups_check_5:
  forallb y_edge_phase_group_check
    (skipn 32 (skipn 32 (skipn 32 (skipn 32 (skipn 32
      y_edge_phases))))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma y_edge_phase_groups_known:
  Forall (fun p => In (edge_phase_group p) y_edge_group_rules)
    y_edge_phases.
Proof.
  eapply y_Forall_split with (n:=32).
  - eapply forallb_sound;
      [exact y_edge_phase_group_check_sound|
       exact y_edge_phase_groups_check_0].
  - eapply y_Forall_split with (n:=32).
    + eapply forallb_sound;
        [exact y_edge_phase_group_check_sound|
         exact y_edge_phase_groups_check_1].
    + eapply y_Forall_split with (n:=32).
      * eapply forallb_sound;
          [exact y_edge_phase_group_check_sound|
           exact y_edge_phase_groups_check_2].
      * eapply y_Forall_split with (n:=32).
        -- eapply forallb_sound;
             [exact y_edge_phase_group_check_sound|
              exact y_edge_phase_groups_check_3].
        -- eapply y_Forall_split with (n:=32).
           ++ eapply forallb_sound;
                [exact y_edge_phase_group_check_sound|
                 exact y_edge_phase_groups_check_4].
           ++ eapply forallb_sound;
                [exact y_edge_phase_group_check_sound|
                 exact y_edge_phase_groups_check_5].
Qed.

Definition y_phase_stream (d:packet_stream_text) :
    Stream (DH0*DH0) :=
  stream_of_text (hashR,hashL) (atSignalR,atSignalL)
    (dollarR,dollarL) d.

Definition y_column_flows : list column_flow_text := [
  mk_column_flow_text ColumnY (mk_packet_stream_text "########################################$" PacketDollar 43) (mk_packet_stream_text "#" PacketDollar 39);
  mk_column_flow_text ColumnY (mk_packet_stream_text "####################################$" PacketDollar 40) (mk_packet_stream_text "" PacketDollar 36);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############################$" PacketDollar 37) (mk_packet_stream_text "###############################@" PacketAt 36);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############################@" PacketAt 36) (mk_packet_stream_text "##############################@" PacketAt 37);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##########################@" PacketAt 37) (mk_packet_stream_text "###########################$" PacketDollar 36);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######################$" PacketDollar 36) (mk_packet_stream_text "######################@" PacketAt 35);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####################@" PacketAt 35) (mk_packet_stream_text "#####################@" PacketAt 36);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#################@" PacketAt 36) (mk_packet_stream_text "##################$" PacketDollar 35);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############$" PacketDollar 35) (mk_packet_stream_text "#############@" PacketAt 34);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########@" PacketAt 34) (mk_packet_stream_text "############@" PacketAt 35);
  mk_column_flow_text ColumnY (mk_packet_stream_text "########@" PacketAt 35) (mk_packet_stream_text "#########$" PacketDollar 34);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####$" PacketDollar 34) (mk_packet_stream_text "####@" PacketAt 33);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##@" PacketAt 33) (mk_packet_stream_text "###@" PacketAt 34);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#############################@" PacketAt 35) (mk_packet_stream_text "##############################$" PacketDollar 34);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########################$" PacketDollar 34) (mk_packet_stream_text "#########################@" PacketAt 33);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####################@" PacketAt 33) (mk_packet_stream_text "#####################@" PacketAt 34);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###################@" PacketAt 34) (mk_packet_stream_text "####################@" PacketAt 35);
  mk_column_flow_text ColumnY (mk_packet_stream_text "################@" PacketAt 35) (mk_packet_stream_text "#################$" PacketDollar 34);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############$" PacketDollar 34) (mk_packet_stream_text "############@" PacketAt 33);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########@" PacketAt 33) (mk_packet_stream_text "###########@" PacketAt 34);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#######@" PacketAt 34) (mk_packet_stream_text "########$" PacketDollar 33);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###$" PacketDollar 33) (mk_packet_stream_text "###@" PacketAt 32);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#@" PacketAt 32) (mk_packet_stream_text "##@" PacketAt 33);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############################@" PacketAt 34) (mk_packet_stream_text "#############################@" PacketAt 35);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############################@" PacketAt 35) (mk_packet_stream_text "##############################@" PacketAt 36);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##############################@" PacketAt 36) (mk_packet_stream_text "###############################@" PacketAt 37);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############################@" PacketAt 37) (mk_packet_stream_text "################################@" PacketAt 38);
  mk_column_flow_text ColumnY (mk_packet_stream_text "############################@" PacketAt 38) (mk_packet_stream_text "#############################$" PacketDollar 37);
  mk_column_flow_text ColumnX (mk_packet_stream_text "########################$" PacketDollar 37) (mk_packet_stream_text "########################@" PacketAt 36);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######################@" PacketAt 36) (mk_packet_stream_text "#######################@" PacketAt 37);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###################@" PacketAt 37) (mk_packet_stream_text "####################$" PacketDollar 36);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############$" PacketDollar 36) (mk_packet_stream_text "###############@" PacketAt 35);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############@" PacketAt 35) (mk_packet_stream_text "##############@" PacketAt 36);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##########@" PacketAt 36) (mk_packet_stream_text "###########$" PacketDollar 35);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######$" PacketDollar 35) (mk_packet_stream_text "######@" PacketAt 34);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####@" PacketAt 34) (mk_packet_stream_text "#####@" PacketAt 35);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#@" PacketAt 35) (mk_packet_stream_text "##$" PacketDollar 34);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################$" PacketDollar 35) (mk_packet_stream_text "##########################@" PacketAt 34);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####################@" PacketAt 34) (mk_packet_stream_text "######################@" PacketAt 35);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###################@" PacketAt 35) (mk_packet_stream_text "####################@" PacketAt 36);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####################@" PacketAt 36) (mk_packet_stream_text "#####################@" PacketAt 37);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####################@" PacketAt 37) (mk_packet_stream_text "#####################@" PacketAt 38);
  mk_column_flow_text ColumnX (mk_packet_stream_text "################@" PacketAt 38) (mk_packet_stream_text "#################@" PacketAt 39);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############@" PacketAt 39) (mk_packet_stream_text "#############@" PacketAt 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########@" PacketAt 40) (mk_packet_stream_text "############@" PacketAt 41);
  mk_column_flow_text ColumnY (mk_packet_stream_text "########@" PacketAt 41) (mk_packet_stream_text "#########$" PacketDollar 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####$" PacketDollar 40) (mk_packet_stream_text "####@" PacketAt 39);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##@" PacketAt 39) (mk_packet_stream_text "###@" PacketAt 40);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###################################@" PacketAt 41) (mk_packet_stream_text "####################################$" PacketDollar 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############################$" PacketDollar 40) (mk_packet_stream_text "###############################@" PacketAt 39);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################@" PacketAt 39) (mk_packet_stream_text "###########################@" PacketAt 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########################@" PacketAt 40) (mk_packet_stream_text "##########################@" PacketAt 41);
  mk_column_flow_text ColumnY (mk_packet_stream_text "######################@" PacketAt 41) (mk_packet_stream_text "#######################$" PacketDollar 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################$" PacketDollar 40) (mk_packet_stream_text "##################@" PacketAt 39);
  mk_column_flow_text ColumnX (mk_packet_stream_text "################@" PacketAt 39) (mk_packet_stream_text "#################@" PacketAt 40);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#############@" PacketAt 40) (mk_packet_stream_text "##############$" PacketDollar 39);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########$" PacketDollar 39) (mk_packet_stream_text "#########@" PacketAt 38);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######@" PacketAt 38) (mk_packet_stream_text "########@" PacketAt 39);
  mk_column_flow_text ColumnY (mk_packet_stream_text "####@" PacketAt 39) (mk_packet_stream_text "#####$" PacketDollar 38);
  mk_column_flow_text ColumnX (mk_packet_stream_text "$" PacketDollar 38) (mk_packet_stream_text "@" PacketAt 37);
  mk_column_flow_text ColumnX (mk_packet_stream_text "################################@" PacketAt 38) (mk_packet_stream_text "#################################@" PacketAt 39);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############################@" PacketAt 39) (mk_packet_stream_text "#############################@" PacketAt 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########################@" PacketAt 40) (mk_packet_stream_text "############################@" PacketAt 41);
  mk_column_flow_text ColumnY (mk_packet_stream_text "########################@" PacketAt 41) (mk_packet_stream_text "#########################$" PacketDollar 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####################$" PacketDollar 40) (mk_packet_stream_text "####################@" PacketAt 39);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################@" PacketAt 39) (mk_packet_stream_text "###################@" PacketAt 40);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###############@" PacketAt 40) (mk_packet_stream_text "################$" PacketDollar 39);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########$" PacketDollar 39) (mk_packet_stream_text "###########@" PacketAt 38);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########@" PacketAt 38) (mk_packet_stream_text "##########@" PacketAt 39);
  mk_column_flow_text ColumnY (mk_packet_stream_text "######@" PacketAt 39) (mk_packet_stream_text "#######$" PacketDollar 38);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##$" PacketDollar 38) (mk_packet_stream_text "##@" PacketAt 37);
  mk_column_flow_text ColumnX (mk_packet_stream_text "@" PacketAt 37) (mk_packet_stream_text "#@" PacketAt 38);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############################@" PacketAt 39) (mk_packet_stream_text "################################@" PacketAt 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########################@" PacketAt 40) (mk_packet_stream_text "############################@" PacketAt 41);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######################@" PacketAt 41) (mk_packet_stream_text "########################@" PacketAt 42);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######################@" PacketAt 42) (mk_packet_stream_text "#######################@" PacketAt 43);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###################@" PacketAt 43) (mk_packet_stream_text "####################$" PacketDollar 42);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############$" PacketDollar 42) (mk_packet_stream_text "###############@" PacketAt 41);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############@" PacketAt 41) (mk_packet_stream_text "##############@" PacketAt 42);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##########@" PacketAt 42) (mk_packet_stream_text "###########$" PacketDollar 41);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######$" PacketDollar 41) (mk_packet_stream_text "######@" PacketAt 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####@" PacketAt 40) (mk_packet_stream_text "#####@" PacketAt 41);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#@" PacketAt 41) (mk_packet_stream_text "##$" PacketDollar 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "################################$" PacketDollar 41) (mk_packet_stream_text "################################@" PacketAt 40);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########################@" PacketAt 40) (mk_packet_stream_text "############################@" PacketAt 41);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########################@" PacketAt 41) (mk_packet_stream_text "##########################@" PacketAt 42);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################@" PacketAt 42) (mk_packet_stream_text "###########################@" PacketAt 43);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################@" PacketAt 43) (mk_packet_stream_text "###########################@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######################@" PacketAt 44) (mk_packet_stream_text "#######################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################@" PacketAt 45) (mk_packet_stream_text "###################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#################@" PacketAt 46) (mk_packet_stream_text "##################@" PacketAt 47);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##############@" PacketAt 47) (mk_packet_stream_text "###############$" PacketDollar 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########$" PacketDollar 46) (mk_packet_stream_text "##########@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "########@" PacketAt 45) (mk_packet_stream_text "#########@" PacketAt 46);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#####@" PacketAt 46) (mk_packet_stream_text "######$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#$" PacketDollar 45) (mk_packet_stream_text "#@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################################@" PacketAt 45) (mk_packet_stream_text "###########################################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######################################@" PacketAt 46) (mk_packet_stream_text "########################################@" PacketAt 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###################################@" PacketAt 47) (mk_packet_stream_text "####################################@" PacketAt 48);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################################@" PacketAt 48) (mk_packet_stream_text "###################################@" PacketAt 49);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###############################@" PacketAt 49) (mk_packet_stream_text "################################$" PacketDollar 48);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########################$" PacketDollar 48) (mk_packet_stream_text "###########################@" PacketAt 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########################@" PacketAt 47) (mk_packet_stream_text "##########################@" PacketAt 48);
  mk_column_flow_text ColumnY (mk_packet_stream_text "######################@" PacketAt 48) (mk_packet_stream_text "#######################$" PacketDollar 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################$" PacketDollar 47) (mk_packet_stream_text "##################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "################@" PacketAt 46) (mk_packet_stream_text "#################@" PacketAt 47);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#############@" PacketAt 47) (mk_packet_stream_text "##############$" PacketDollar 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########$" PacketDollar 46) (mk_packet_stream_text "#########@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######@" PacketAt 45) (mk_packet_stream_text "########@" PacketAt 46);
  mk_column_flow_text ColumnY (mk_packet_stream_text "####@" PacketAt 46) (mk_packet_stream_text "#####$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "$" PacketDollar 45) (mk_packet_stream_text "@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######################################@" PacketAt 45) (mk_packet_stream_text "########################################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###################################@" PacketAt 46) (mk_packet_stream_text "####################################@" PacketAt 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################################@" PacketAt 47) (mk_packet_stream_text "###################################@" PacketAt 48);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###############################@" PacketAt 48) (mk_packet_stream_text "################################$" PacketDollar 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########################$" PacketDollar 47) (mk_packet_stream_text "###########################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########################@" PacketAt 46) (mk_packet_stream_text "##########################@" PacketAt 47);
  mk_column_flow_text ColumnY (mk_packet_stream_text "######################@" PacketAt 47) (mk_packet_stream_text "#######################$" PacketDollar 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################$" PacketDollar 46) (mk_packet_stream_text "##################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "################@" PacketAt 45) (mk_packet_stream_text "#################@" PacketAt 46);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#############@" PacketAt 46) (mk_packet_stream_text "##############$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########$" PacketDollar 45) (mk_packet_stream_text "#########@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######@" PacketAt 44) (mk_packet_stream_text "########@" PacketAt 45);
  mk_column_flow_text ColumnY (mk_packet_stream_text "####@" PacketAt 45) (mk_packet_stream_text "#####$" PacketDollar 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "$" PacketDollar 44) (mk_packet_stream_text "@" PacketAt 43);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######################################@" PacketAt 44) (mk_packet_stream_text "#######################################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################################@" PacketAt 45) (mk_packet_stream_text "###################################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#################################@" PacketAt 46) (mk_packet_stream_text "##################################@" PacketAt 47);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##############################@" PacketAt 47) (mk_packet_stream_text "###############################$" PacketDollar 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################$" PacketDollar 46) (mk_packet_stream_text "##########################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "########################@" PacketAt 45) (mk_packet_stream_text "#########################@" PacketAt 46);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#####################@" PacketAt 46) (mk_packet_stream_text "######################$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#################$" PacketDollar 45) (mk_packet_stream_text "#################@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############@" PacketAt 44) (mk_packet_stream_text "################@" PacketAt 45);
  mk_column_flow_text ColumnY (mk_packet_stream_text "############@" PacketAt 45) (mk_packet_stream_text "#############$" PacketDollar 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "########$" PacketDollar 44) (mk_packet_stream_text "########@" PacketAt 43);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######@" PacketAt 43) (mk_packet_stream_text "#######@" PacketAt 44);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###@" PacketAt 44) (mk_packet_stream_text "####$" PacketDollar 43);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########################################$" PacketDollar 44) (mk_packet_stream_text "#########################################@" PacketAt 43);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####################################@" PacketAt 43) (mk_packet_stream_text "######################################@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#################################@" PacketAt 44) (mk_packet_stream_text "##################################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############################@" PacketAt 45) (mk_packet_stream_text "##############################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############################@" PacketAt 46) (mk_packet_stream_text "#############################@" PacketAt 47);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#########################@" PacketAt 47) (mk_packet_stream_text "##########################$" PacketDollar 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####################$" PacketDollar 46) (mk_packet_stream_text "#####################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###################@" PacketAt 45) (mk_packet_stream_text "####################@" PacketAt 46);
  mk_column_flow_text ColumnY (mk_packet_stream_text "################@" PacketAt 46) (mk_packet_stream_text "#################$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############$" PacketDollar 45) (mk_packet_stream_text "############@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########@" PacketAt 44) (mk_packet_stream_text "###########@" PacketAt 45);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#######@" PacketAt 45) (mk_packet_stream_text "########$" PacketDollar 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###$" PacketDollar 44) (mk_packet_stream_text "###@" PacketAt 43);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#@" PacketAt 43) (mk_packet_stream_text "##@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######################################@" PacketAt 45) (mk_packet_stream_text "########################################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "########################################@" PacketAt 46) (mk_packet_stream_text "#########################################@" PacketAt 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########################################@" PacketAt 47) (mk_packet_stream_text "##########################################@" PacketAt 48);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################################@" PacketAt 48) (mk_packet_stream_text "###########################################@" PacketAt 49);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#######################################@" PacketAt 49) (mk_packet_stream_text "########################################$" PacketDollar 48);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###################################$" PacketDollar 48) (mk_packet_stream_text "###################################@" PacketAt 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#################################@" PacketAt 47) (mk_packet_stream_text "##################################@" PacketAt 48);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##############################@" PacketAt 48) (mk_packet_stream_text "###############################$" PacketDollar 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################$" PacketDollar 47) (mk_packet_stream_text "##########################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "########################@" PacketAt 46) (mk_packet_stream_text "#########################@" PacketAt 47);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#####################@" PacketAt 47) (mk_packet_stream_text "######################$" PacketDollar 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#################$" PacketDollar 46) (mk_packet_stream_text "#################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############@" PacketAt 45) (mk_packet_stream_text "################@" PacketAt 46);
  mk_column_flow_text ColumnY (mk_packet_stream_text "############@" PacketAt 46) (mk_packet_stream_text "#############$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "########$" PacketDollar 45) (mk_packet_stream_text "########@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######@" PacketAt 44) (mk_packet_stream_text "#######@" PacketAt 45);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###@" PacketAt 45) (mk_packet_stream_text "####$" PacketDollar 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########################################$" PacketDollar 45) (mk_packet_stream_text "##########################################@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######################################@" PacketAt 44) (mk_packet_stream_text "#######################################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################################@" PacketAt 45) (mk_packet_stream_text "###################################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##############################@" PacketAt 46) (mk_packet_stream_text "###############################@" PacketAt 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############################@" PacketAt 47) (mk_packet_stream_text "##############################@" PacketAt 48);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##########################@" PacketAt 48) (mk_packet_stream_text "###########################$" PacketDollar 47);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######################$" PacketDollar 47) (mk_packet_stream_text "######################@" PacketAt 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####################@" PacketAt 46) (mk_packet_stream_text "#####################@" PacketAt 47);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#################@" PacketAt 47) (mk_packet_stream_text "##################$" PacketDollar 46);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############$" PacketDollar 46) (mk_packet_stream_text "#############@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########@" PacketAt 45) (mk_packet_stream_text "############@" PacketAt 46);
  mk_column_flow_text ColumnY (mk_packet_stream_text "########@" PacketAt 46) (mk_packet_stream_text "#########$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####$" PacketDollar 45) (mk_packet_stream_text "####@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##@" PacketAt 44) (mk_packet_stream_text "###@" PacketAt 45);
  mk_column_flow_text ColumnY (mk_packet_stream_text "########################################@" PacketAt 46) (mk_packet_stream_text "#########################################$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####################################$" PacketDollar 45) (mk_packet_stream_text "####################################@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############################@" PacketAt 44) (mk_packet_stream_text "################################@" PacketAt 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##############################@" PacketAt 45) (mk_packet_stream_text "###############################@" PacketAt 46);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###########################@" PacketAt 46) (mk_packet_stream_text "############################$" PacketDollar 45);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######################$" PacketDollar 45) (mk_packet_stream_text "#######################@" PacketAt 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####################@" PacketAt 44) (mk_packet_stream_text "######################@" PacketAt 45);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##################@" PacketAt 45) (mk_packet_stream_text "###################$" PacketDollar 44);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##############$" PacketDollar 44) (mk_packet_stream_text "##############@" PacketAt 43);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############@" PacketAt 43) (mk_packet_stream_text "#############@" PacketAt 44);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#########@" PacketAt 44) (mk_packet_stream_text "##########$" PacketDollar 43);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####$" PacketDollar 43) (mk_packet_stream_text "#####@" PacketAt 42);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###@" PacketAt 42) (mk_packet_stream_text "####@" PacketAt 43);
  mk_column_flow_text ColumnY (mk_packet_stream_text "@" PacketAt 43) (mk_packet_stream_text "#$" PacketDollar 42)
].

Definition y_column_flow_sound (f:column_flow_text) : Prop :=
  downRect tm (y_phase_stream (column_flow_input f))
    (y_phase_stream (column_flow_output f))
    (match column_flow_symbol f with ColumnX => cellX | ColumnY => cellY end) 1.


Ltac y_flow cert :=
  unfold y_column_flow_sound, y_phase_stream;
  cbn [stream_of_text signal_word_of_string]; exact cert.

Lemma y_column_flows_sound:
  Forall y_column_flow_sound y_column_flows.
Proof.
  unfold y_column_flows.
  apply Forall_cons; [y_flow (Y_dollar_column_downRect_normalized 1 39)|].
  apply Forall_cons; [y_flow (Y_dollar_column_downRect_normalized 0 36)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 31 36)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 29 36)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 26 35)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 22 35)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 20 35)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 17 34)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 13 34)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 11 34)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 8 33)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 4 33)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 2 33)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 29 33)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 25 33)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 20 33)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 19 34)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 16 33)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 12 33)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 10 33)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 7 32)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 3 32)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 1 32)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 28 34)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 29 35)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 30 36)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 31 37)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 28 36)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 24 36)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 22 36)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 19 35)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 15 35)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 13 35)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 10 34)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 6 34)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 4 34)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 1 33)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 26 34)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 21 34)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 19 35)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 20 36)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 20 37)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 16 38)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 12 39)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 11 40)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 8 39)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 4 39)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 2 39)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 35 39)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 31 39)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 26 39)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 25 40)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 22 39)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 18 39)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 16 39)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 13 38)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 9 38)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 7 38)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 4 37)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 0 37)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 32 38)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 28 39)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 27 40)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 24 39)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 20 39)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 18 39)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 15 38)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 11 38)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 9 38)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 6 37)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 2 37)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 0 37)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 31 39)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 27 40)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 23 41)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 22 42)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 19 41)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 15 41)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 13 41)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 10 40)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 6 40)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 4 40)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 1 39)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 32 40)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 27 40)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 25 41)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 26 42)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 26 43)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 22 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 18 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 17 46)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 14 45)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 10 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 8 45)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 5 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 1 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 42 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 39 46)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 35 47)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 34 48)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 31 47)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 27 47)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 25 47)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 22 46)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 18 46)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 16 46)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 13 45)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 9 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 7 45)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 4 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 0 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 39 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 35 46)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 34 47)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 31 46)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 27 46)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 25 46)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 22 45)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 18 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 16 45)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 13 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 9 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 7 44)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 4 43)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 0 43)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 38 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 34 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 33 46)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 30 45)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 26 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 24 45)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 21 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 17 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 15 44)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 12 43)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 8 43)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 6 43)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 3 42)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 41 43)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 37 43)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 33 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 29 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 28 46)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 25 45)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 21 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 19 45)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 16 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 12 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 10 44)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 7 43)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 3 43)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 1 43)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 39 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 40 46)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 41 47)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 42 48)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 39 47)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 35 47)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 33 47)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 30 46)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 26 46)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 24 46)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 21 45)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 17 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 15 45)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 12 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 8 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 6 44)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 3 43)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 42 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 38 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 34 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 30 46)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 29 47)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 26 46)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 22 46)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 20 46)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 17 45)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 13 45)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 11 45)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 8 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 4 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 2 44)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 40 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 36 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 31 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 30 45)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 27 44)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 23 44)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 21 44)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 18 43)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 14 43)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 12 43)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 9 42)|].
  apply Forall_cons; [y_flow (X_dollar_column_downRect 5 42)|].
  apply Forall_cons; [y_flow (X_at_column_downRect 3 42)|].
  apply Forall_cons; [y_flow (Y_at_column_downRect 0 41)|].
  apply Forall_nil.
Qed.

Definition y_phase_columns : list (list column_flow_text) :=
  partition_phase_columns y_edge_phases
    (tl y_column_flows ++
      [hd default_column_flow y_column_flows]).


Definition y_column_symbol_eqb (a b:column_symbol) : bool :=
  match a,b with
  | ColumnX,ColumnX | ColumnY,ColumnY => true
  | _,_ => false
  end.

Lemma y_column_symbol_eqb_eq a b:
  y_column_symbol_eqb a b = true <-> a = b.
Proof. destruct a,b; cbn; split; congruence. Qed.

Fixpoint y_column_symbols_eqb
    (xs ys:list column_symbol) : bool :=
  match xs,ys with
  | [],[] => true
  | x::xs',y::ys' =>
      y_column_symbol_eqb x y &&
        y_column_symbols_eqb xs' ys'
  | _,_ => false
  end.

Lemma y_column_symbols_eqb_eq xs ys:
  y_column_symbols_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; cbn;
    try (split; congruence).
  rewrite Bool.andb_true_iff, y_column_symbol_eqb_eq, IH.
  split.
  - intros [-> ->]; reflexivity.
  - intro H; inversion H; auto.
Qed.

Fixpoint y_column_flows_linked_check
    (fs:list column_flow_text) : bool :=
  match fs with
  | [] | [_] => true
  | f::((g::_) as fs') =>
      packet_stream_text_eqb
        (column_flow_output f) (column_flow_input g) &&
      y_column_flows_linked_check fs'
  end.

Lemma y_column_flows_linked_check_sound fs:
  y_column_flows_linked_check fs = true -> column_flows_linked fs.
Proof.
  induction fs as [|f fs IH]; cbn; intro H; [exact I|].
  destruct fs as [|g fs]; cbn in *; [exact I|].
  apply Bool.andb_true_iff in H as [Hfg Htail].
  split.
  - apply packet_stream_text_eqb_eq; exact Hfg.
  - apply IH; exact Htail.
Qed.

Definition y_phase_columns_match_check
    (p:edge_phase_text) (fs:list column_flow_text) : bool :=
  match fs with
  | [] => false
  | f::fs' =>
      packet_stream_text_eqb
        (column_flow_input f) (edge_phase_tail p) &&
      (packet_stream_text_eqb
        (column_flow_output (last (f::fs') default_column_flow))
        (edge_phase_next_stream p) &&
      (y_column_flows_linked_check (f::fs') &&
      y_column_symbols_eqb (map column_flow_symbol (f::fs'))
        (column_symbols_of_string
          (edge_group_emit (edge_phase_group p)))))
  end.

Lemma y_phase_columns_match_check_sound p fs:
  y_phase_columns_match_check p fs = true ->
  phase_columns_match p fs.
Proof.
  destruct fs as [|f fs]; cbn [y_phase_columns_match_check];
    intro H; [discriminate|].
  apply Bool.andb_true_iff in H as [Hin H].
  apply Bool.andb_true_iff in H as [Hout H].
  apply Bool.andb_true_iff in H as [Hlinked Hsymbols].
  unfold phase_columns_match; cbn [hd].
  repeat split.
  - discriminate.
  - apply packet_stream_text_eqb_eq; exact Hin.
  - apply packet_stream_text_eqb_eq; exact Hout.
  - apply y_column_flows_linked_check_sound; exact Hlinked.
  - apply y_column_symbols_eqb_eq; exact Hsymbols.
Qed.

Fixpoint y_forall2b {A B}
    (check:A->B->bool) (xs:list A) (ys:list B) : bool :=
  match xs,ys with
  | [],[] => true
  | x::xs',y::ys' => check x y && y_forall2b check xs' ys'
  | _,_ => false
  end.

Lemma y_forall2b_sound {A B} (check:A->B->bool) (R:A->B->Prop):
  (forall x y, check x y = true -> R x y) ->
  forall xs ys, y_forall2b check xs ys = true -> Forall2 R xs ys.
Proof.
  intros Hsound xs; induction xs as [|x xs IH]; intros [|y ys]; cbn;
    intro H; try discriminate; [constructor|].
  apply Bool.andb_true_iff in H as [Hxy Hrest].
  constructor; [apply Hsound; exact Hxy|apply IH; exact Hrest].
Qed.

Lemma y_phase_columns_match:
  Forall2 phase_columns_match y_edge_phases y_phase_columns.
Proof.
  eapply y_forall2b_sound.
  - exact y_phase_columns_match_check_sound.
  - vm_compute; reflexivity.
Qed.

Lemma y_rotated_column_flows_sound:
  Forall y_column_flow_sound
    (tl y_column_flows ++
      [hd default_column_flow y_column_flows]).
Proof.
  apply Forall_rotate_local.
  - vm_compute; discriminate.
  - exact y_column_flows_sound.
Qed.

Lemma y_phase_columns_flows_sound:
  Forall (Forall y_column_flow_sound) y_phase_columns.
Proof.
  unfold y_phase_columns.
  apply partition_phase_columns_Forall.
  exact y_rotated_column_flows_sound.
Qed.

Definition y_column_symbol_word (s:column_symbol) : list Sym :=
  match s with ColumnX => cellX | ColumnY => cellY end.

Fixpoint y_column_flow_word (fs:list column_flow_text) : list Sym :=
  match fs with
  | [] => []
  | f::fs' => y_column_symbol_word (column_flow_symbol f) ++
      y_column_flow_word fs'
  end.

Fixpoint y_column_symbols_word (ss:list column_symbol) : list Sym :=
  match ss with
  | [] => []
  | s::ss' => y_column_symbol_word s ++
      y_column_symbols_word ss'
  end.

Lemma y_column_flow_word_symbols fs:
  y_column_flow_word fs =
    y_column_symbols_word (map column_flow_symbol fs).
Proof. induction fs; cbn; rewrite ?IHfs; reflexivity. Qed.

Lemma y_column_word_of_string_symbols s:
  column_word_of_string cellX cellY s =
    y_column_symbols_word (column_symbols_of_string s).
Proof.
  induction s as [|a s IH]; cbn
    [column_word_of_string column_symbols_of_string
      y_column_symbols_word y_column_symbol_word].
  - reflexivity.
  - destruct (Nat.eqb (nat_of_ascii a) 88); rewrite IH; reflexivity.
Qed.

Lemma y_column_flow_chain_downRect fs:
  fs <> [] ->
  Forall y_column_flow_sound fs ->
  column_flows_linked fs ->
  downRect tm
    (y_phase_stream (column_flow_input
      (hd default_column_flow fs)))
    (y_phase_stream (column_flow_output
      (last fs default_column_flow)))
    (y_column_flow_word fs) (length fs).
Proof.
  induction fs as [|f fs IH]; intros Hne Hsound Hlinked.
  - contradiction.
  - destruct fs as [|g fs].
    + inversion Hsound; subst.
      unfold y_column_flow_sound in H1.
      cbn [y_column_flow_word y_column_symbol_word hd last].
      rewrite app_nil_r.
      change (downRect tm
        (y_phase_stream (column_flow_input f))
        (y_phase_stream (column_flow_output f))
        (y_column_symbol_word (column_flow_symbol f)) 1).
      unfold y_column_symbol_word.
      exact H1.
    + inversion Hsound as [|? ? Hf Htail]; subst.
      cbn [column_flows_linked] in Hlinked.
      destruct Hlinked as [Hfg Hlinked].
      specialize (IH ltac:(discriminate) Htail Hlinked).
      unfold y_column_flow_sound in Hf.
      rewrite Hfg in Hf.
      pose proof (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
        Hf IH) as Hcat.
      cbn [y_column_flow_word y_column_symbol_word hd last] in *.
      exact Hcat.
Qed.

Lemma y_phase_columns_downRect p fs:
  phase_columns_match p fs ->
  Forall y_column_flow_sound fs ->
  downRect tm (y_phase_stream (edge_phase_tail p))
    (y_phase_stream (edge_phase_next_stream p))
    (column_word_of_string cellX cellY
      (edge_group_emit (edge_phase_group p)))
    (length fs).
Proof.
  intros [Hne [Hin [Hout [Hlinked Hsymbols]]]] Hsound.
  pose proof (y_column_flow_chain_downRect fs Hne Hsound Hlinked)
    as Hrect.
  rewrite Hin, Hout in Hrect.
  rewrite y_column_flow_word_symbols, Hsymbols,
    <- y_column_word_of_string_symbols in Hrect.
  exact Hrect.
Qed.

Lemma y_edge_phase_downRects:
  Forall2 (fun p fs =>
    downRect tm (y_phase_stream (edge_phase_tail p))
      (y_phase_stream (edge_phase_next_stream p))
      (column_word_of_string cellX cellY
        (edge_group_emit (edge_phase_group p)))
      (length fs))
    y_edge_phases y_phase_columns.
Proof.
  pose proof y_phase_columns_match as Hmatch.
  pose proof y_phase_columns_flows_sound as Hsound.
  induction Hmatch; inversion Hsound; subst; constructor.
  - eapply y_phase_columns_downRect; eauto.
  - apply IHHmatch; assumption.
Qed.

Definition y_next_phases : list edge_phase_text :=
  tl y_edge_phases ++ [hd
    (mk_edge_phase_text
      (mk_edge_group_text "" "" "" "")
      (mk_packet_stream_text "" PacketAt 0)
      (mk_packet_stream_text "" PacketAt 0)
      (mk_packet_stream_text "" PacketAt 0))
    y_edge_phases].

Definition y_phase_next_match (p q:edge_phase_text) : Prop :=
  edge_group_after (edge_phase_group p) =
    edge_group_before (edge_phase_group q) /\
  edge_phase_next_stream p = edge_phase_stream q.

Definition y_string_eqb (a b:string) : bool :=
  if string_dec a b then true else false.

Lemma y_string_eqb_eq a b:
  y_string_eqb a b = true <-> a = b.
Proof.
  unfold y_string_eqb; destruct (string_dec a b); split; congruence.
Qed.

Definition y_phase_next_match_check
    (p q:edge_phase_text) : bool :=
  y_string_eqb
    (edge_group_after (edge_phase_group p))
    (edge_group_before (edge_phase_group q)) &&
  packet_stream_text_eqb
    (edge_phase_next_stream p) (edge_phase_stream q).

Lemma y_phase_next_match_check_sound p q:
  y_phase_next_match_check p q = true ->
  y_phase_next_match p q.
Proof.
  unfold y_phase_next_match_check, y_phase_next_match.
  rewrite Bool.andb_true_iff.
  intros [Hedge Hstream]; split.
  - apply y_string_eqb_eq; exact Hedge.
  - apply packet_stream_text_eqb_eq; exact Hstream.
Qed.

Lemma y_phase_next_matches:
  Forall2 y_phase_next_match y_edge_phases y_next_phases.
Proof.
  eapply y_forall2b_sound.
  - exact y_phase_next_match_check_sound.
  - vm_compute; reflexivity.
Qed.

Lemma y_In_tl {A} (q:A) xs:
  In q (tl xs) -> In q xs.
Proof. destruct xs; cbn; intuition. Qed.

Lemma y_hd_In {A} (d:A) xs:
  xs <> [] -> In (hd d xs) xs.
Proof. destruct xs; cbn; intuition. Qed.

Lemma y_In_rotate {A} (d:A) xs q:
  xs <> [] -> In q (tl xs ++ [hd d xs]) -> In q xs.
Proof.
  intros Hne H; apply in_app_or in H; destruct H as [H|H].
  - apply y_In_tl; exact H.
  - cbn in H; destruct H as [<-|[]].
    apply y_hd_In; exact Hne.
Qed.


Lemma y_next_phase_in q:
  In q y_next_phases -> In q y_edge_phases.
Proof.
  unfold y_next_phases; apply y_In_rotate.
  vm_compute; discriminate.
Qed.

Lemma y_phase_columns_positive:
  Forall (fun fs => O < length fs) y_phase_columns.
Proof. vm_compute; repeat constructor; lia. Qed.

Lemma y_edge_phases_emit_nonempty:
  Forall (fun p =>
    column_word_of_string cellX cellY
      (edge_group_emit (edge_phase_group p)) <> [])
    y_edge_phases.
Proof. vm_compute; repeat constructor; discriminate. Qed.

Definition y_cycle (L:Stream (DH0*DH0)) (top:side) : Prop :=
  exists p, In p y_edge_phases /\
    L = y_phase_stream (edge_phase_stream p) /\
    top = bit_word_of_string
      (edge_group_before (edge_phase_group p)) *> 0inf.

Lemma y_cycle_dynamic_step L top:
  y_cycle L top -> dynamic_side_step tm y_cycle L top.
Proof.
  intros [p [Hp [HL Htop]]].
  pose proof y_edge_phase_consumes as Hconsume.
  rewrite Forall_forall in Hconsume; specialize (Hconsume p Hp).
  pose proof y_edge_phase_groups_known as Hknown.
  rewrite Forall_forall in Hknown; specialize (Hknown p Hp).
  pose proof y_edge_group_rules_sound as Hedge.
  rewrite Forall_forall in Hedge;
    specialize (Hedge (edge_phase_group p) Hknown).
  destruct (Forall2_In_left_exists _ _ _ p
    y_edge_phase_downRects Hp) as [fs [Hfs Hrect]].
  pose proof y_phase_columns_positive as Hwidth.
  rewrite Forall_forall in Hwidth; specialize (Hwidth fs Hfs).
  pose proof y_edge_phases_emit_nonempty as Hemit.
  rewrite Forall_forall in Hemit; specialize (Hemit p Hp).
  destruct (Forall2_In_left_exists _ _ _ p
    y_phase_next_matches Hp) as [q [Hq Hnext]].
  destruct Hnext as [Hedge_next Hstream_next].
  exists
    (signal_word_of_string hash atSignal dollar
      (edge_group_consume (edge_phase_group p))),
    (y_phase_stream (edge_phase_tail p)),
    (y_phase_stream (edge_phase_next_stream p)),
    (bit_word_of_string (edge_group_after (edge_phase_group p)) *> 0inf),
    (column_word_of_string cellX cellY
      (edge_group_emit (edge_phase_group p))),
    (length fs).
  split; [exact Hwidth|].
  split; [exact Hemit|].
  split.
  - rewrite HL.
    unfold y_phase_stream.
    eapply packet_stream_text_consume_sound; exact Hconsume.
  - split.
    + rewrite Htop. exact Hedge.
    + split; [exact Hrect|].
      exists q. split.
      * apply y_next_phase_in; exact Hq.
      * split.
        -- rewrite Hstream_next. reflexivity.
        -- rewrite <- Hedge_next. reflexivity.
Qed.

Lemma y_cycle_quadRect L top:
  y_cycle L top -> quadRect tm L top.
Proof.
  intro Hcycle.
  apply dynamic_side_unbounded with (P:=y_cycle).
  - exact y_cycle_dynamic_step.
  - exact Hcycle.
Qed.

Notation hashLR := [(hashL,hashR)].
Notation hashLdollarR := [(hashL,dollarR)].
Notation dollarLhR := [(dollarL,hashR)].

Definition y_cut_left (a b:nat) : side :=
  0inf
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1]^^a
  <* <[0;0]
  <* <[1;1;0;1;1;1;1]^^b
  <* <[0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;0;0;1;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;0;0;1;1;1;1;1].

Lemma y_cut_left_shift a b:
  sideRLs (flip tm) hashLR
    (y_cut_left a (1+b)) (y_cut_left (1+a) b).
Proof.
  unfold y_cut_left. es' a b.
Qed.

Lemma y_cut_left_reset a:
  sideRLs (flip tm)
    ((hashLR^^110) ++ hashLdollarR ++ dollarLhR)
    (y_cut_left a O) (y_cut_left O (1+a)).
Proof.
  unfold y_cut_left. es' a.
Qed.

Definition y_left_stream (a b:nat) : Stream (DH0*DH0) :=
  (hash^^(b+111)) *> dollar *> dollar_packets (a+b+112).

Lemma y_left_stream_shift a b:
  y_left_stream a (1+b) =
    hash *> y_left_stream (1+a) b.
Proof.
  unfold y_left_stream.
  replace (1 + b + 111) with (S (b+111)) by lia.
  rewrite lpow_S, Str_app_assoc.
  replace (a + (1 + b) + 112) with (1 + a + b + 112) by lia.
  reflexivity.
Qed.

Lemma y_left_stream_new_packet a:
  y_left_stream O (1+a) = dollar_packets (a+112).
Proof.
  unfold y_left_stream.
  replace (1 + a + 111) with (a+112) by lia.
  replace (0 + (1 + a) + 112) with (S (a+112)) by lia.
  rewrite <- Str_app_assoc.
  unfold dollar_packets.
  rewrite <- repeat_singleton_lpow.
  symmetry. apply growing_packets_unfold.
Qed.

Lemma y_left_stream_reset a:
  y_left_stream a O =
    ((hash^^111) ++ dollar) *> y_left_stream O (1+a).
Proof.
  unfold y_left_stream at 1.
  cbn [Nat.add].
  rewrite y_left_stream_new_packet.
  replace (a + 0 + 112) with (a+112) by lia.
  rewrite Str_app_assoc. reflexivity.
Qed.

Lemma y_left_stream_initial:
  y_left_stream O O = dollar_packets 111.
Proof.
  unfold y_left_stream.
  cbn [Nat.add].
  rewrite <- Str_app_assoc.
  unfold dollar_packets.
  rewrite <- repeat_singleton_lpow.
  symmetry. apply growing_packets_unfold.
Qed.

Inductive YLeftBoundaryState :
    DH0 -> Stream (DH0*DH0) -> side -> Prop :=
| YLBS a b : YLeftBoundaryState hashR
    (y_left_stream a b) (y_cut_left a b).

Lemma y_cut_left_realizes:
  leftRealizes tm hashR (dollar_packets 111)
    (y_cut_left O O).
Proof.
  rewrite <- y_left_stream_initial.
  eapply leftRealizes_inf_concat with (P:=YLeftBoundaryState).
  - intros h0 L l Hstate. inversion Hstate as [a b]; subst.
    destruct b as [|b].
    + exists ((hash^^111)++dollar),
        (y_left_stream O (1+a)), hashR,
        ((hashLR^^110)++hashLdollarR++dollarLhR),
        (y_cut_left O (1+a)).
      split; [change (O < 112); lia|].
      split; [apply y_left_stream_reset|].
      split; [reflexivity|].
      split; [apply y_cut_left_reset|constructor].
    + exists hash, (y_left_stream (1+a) b), hashR, hashLR,
        (y_cut_left (1+a) b).
      split; [cbn; lia|].
      split; [apply y_left_stream_shift|].
      split; [reflexivity|].
      split; [apply y_cut_left_shift|constructor].
  - constructor.
Qed.

Definition y_initial_column_symbol_word
    (s:ordinary_column_symbol) : list Sym :=
  match s with
  | OrdinaryX => cellX | OrdinaryY => cellY | OrdinaryH => cellH
  | OrdinaryD => cellD | OrdinaryP => cellP | OrdinaryQ => cellQ
  end.

Definition y_event111_edge_side : side :=
  bit_word_of_string "111001110001111" *> 0inf.

Definition y_event111_edge_stream : Stream (DH0*DH0) :=
  (hash^^8) *> atSignal *> at_packets 44.

Lemma y_event111_edge_until_emit:
  sideRLs tm hash y_event111_edge_side
    (cellX *> (bit_word_of_string "11100001" *> 0inf)).
Proof.
  unfold y_event111_edge_side.
  cbn [bit_word_of_string]. esc.
Qed.

Definition y_event111_cycle_phase : edge_phase_text :=
  mk_edge_phase_text
    (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "########@" PacketAt 45)
    (mk_packet_stream_text "####@" PacketAt 45)
    (mk_packet_stream_text "#####$" PacketDollar 44).

Lemma y_event111_cycle_phase_in:
  In y_event111_cycle_phase y_edge_phases.
Proof. vm_compute; tauto. Qed.

Lemma y_event111_cycle_quadRect:
  quadRect tm ((hash^^8) *> atSignal *> at_packets 45)
    (bit_word_of_string "11100001" *> 0inf).
Proof.
  apply y_cycle_quadRect.
  exists y_event111_cycle_phase.
  split; [exact y_event111_cycle_phase_in|].
  split; reflexivity.
Qed.

Lemma y_event111_edge_quadRect:
  quadRect tm y_event111_edge_stream y_event111_edge_side.
Proof.
  unfold y_event111_edge_stream.
  rewrite lpow_S, Str_app_assoc.
  eapply sideRLs_downRect_quadRect
    with (Ltail:=((hash^^7) *> atSignal *> at_packets 44))
      (Ledge:=((hash^^8) *> atSignal *> at_packets 45))
      (top':=(bit_word_of_string "11100001" *> 0inf))
      (w:=cellX) (width:=1%nat).
  - lia.
  - exact y_event111_edge_until_emit.
  - exact (X_at_column_downRect 7 44).
  - exact y_event111_cycle_quadRect.
Qed.

(* The exact 775 ordinary columns to the right of the event-111 cut.
   Each refinement below carries the full parameterized input/output stream
   and [downRect_concat] checks the phase match with its neighbour. *)
Definition y_event111_suffix_symbols : list ordinary_column_symbol := [
  OrdinaryP; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryY; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryD; OrdinaryP; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryP; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryY; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryD; OrdinaryP; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryY; OrdinaryY; OrdinaryP; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryH; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryD; OrdinaryP;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryY; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryD; OrdinaryP; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryH; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX
].

Definition y_event111_suffix_word : list Sym :=
  fold_right (fun s w => y_initial_column_symbol_word s ++ w) []
    y_event111_suffix_symbols.


Lemma y_event111_suffix_downRect:
  downRect tm (dollar_packets 111) y_event111_edge_stream
    y_event111_suffix_word 775%nat.
Proof.
  assert (Hrect: downRect tm (dollar_packets 111)
    ((hash^^8) *> atSignal *> at_packets 44)
    y_event111_suffix_word 775%nat).
  {
  unfold y_event111_suffix_word, y_event111_suffix_symbols,
    y_initial_column_symbol_word.
  cbn [fold_right].
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 3 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 5 112) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 6 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 7 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 7 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 8 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 9 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 9 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 10 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 11 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 11 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 12 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 14 112) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 15 113) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 16 112) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 17 112) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 17 112) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 18 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 19 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 19 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 20 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 21 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 22 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 23 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 24 108) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 25 108) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 108) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 26 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 28 111) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 29 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 30 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 30 110) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 31 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 32 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 32 109) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 33 108) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 34 108) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 34 108) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 35 107) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 36 107) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 36 107) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 37 108) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 38 107) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 39 107) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 39 107) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 40 106) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 41 106) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 41 106) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 42 105) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 43 105) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 43 105) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 44 104) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 45 102) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 45 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 45 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 45 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 46 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 47 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 47 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 48 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 49 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 49 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 50 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 51 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 51 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 52 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 53 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 53 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 54 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 55 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 56 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 56 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 57 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 58 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 58 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 59 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 60 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 61 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 62 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 63 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 64 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 64 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 65 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 66 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 66 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 67 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 68 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 68 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 69 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 70 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 70 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 71 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 72 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 73 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 74 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 75 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 76 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 77 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 78 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 78 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 79 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 80 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 80 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 81 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 82 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 83 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 83 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 84 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 85 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 85 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 86 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 87 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 87 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 88 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 89 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 90 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 91 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 91 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 92 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 93 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 93 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (D_at_column_downRect 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 1 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 3 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 5 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 6 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 6 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 7 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 8 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 8 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 9 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 10 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 10 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 11 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 12 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 14 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 15 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 16 100) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 17 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 18 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 18 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 19 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 20 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 20 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 22 100) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 101) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 24 100) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 25 100) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 100) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 26 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 27 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 28 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 29 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 29 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 30 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 31 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 31 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 32 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 33 99) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 34 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 35 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 35 98) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 36 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 37 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 37 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 38 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 39 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 39 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 40 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 41 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 41 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 42 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 43 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 44 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 45 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 45 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 46 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 47 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 47 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 48 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 49 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 49 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 50 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 51 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 51 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 52 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 53 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 54 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 55 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 56 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 56 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 57 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 58 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 58 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 59 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 60 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 60 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 61 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 62 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 63 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 64 97) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 65 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 66 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 66 96) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 67 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 68 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 68 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 69 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 70 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 70 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 71 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 72 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 72 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 73 92) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 74 92) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 74 92) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 75 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 76 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 77 95) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 78 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 79 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 79 94) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 80 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 81 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 81 93) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 82 92) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 83 92) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 83 92) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 84 91) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 85 91) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 85 91) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 86 92) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 87 91) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 88 91) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 88 91) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect_normalized 89) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 89) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 89) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 88) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 88) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 88) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 3 87) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 4 85) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 4 82) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 4 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 5 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 6 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 6 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 7 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 8 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 8 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 9 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 10 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 10 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 11 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 12 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 12 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 14 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 15 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 15 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 16 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 17 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 17 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 18 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 19 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 20 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 22 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 23 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 24 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 25 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 26 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 27 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 28 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 29 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 29 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 30 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 31 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 32 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 33 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 34 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 35 82) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 36 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 37 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 37 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 38 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 39 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 39 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 40 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 41 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 42 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 42 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 43 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 44 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 44 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 45 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 46 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 46 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 47 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 48 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 49 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 50 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 50 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 51 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 52 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 52 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 53 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 54 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 54 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 55 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 56 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 57 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 58 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 59 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 60 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 60 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 61 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 62 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 62 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 63 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 64 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 64 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 65 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 66 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 67 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 68 82) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 69 83) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 70 84) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 71 83) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 72 83) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 72 83) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 73 82) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 74 82) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 74 82) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 75 83) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 76 84) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 77 85) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 78 84) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 79 84) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 79 84) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 80 83) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 81 83) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 81 83) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (D_at_column_downRect 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 3 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 82) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 5 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 6 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 6 81) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 7 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 8 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 8 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 9 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 10 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 10 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 11 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 12 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 12 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 14 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 15 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 16 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 16 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 17 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 18 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 18 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 19 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 20 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 20 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 21 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 22 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 22 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 24 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 26 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 27 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 28 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 29 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 29 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 30 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 31 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 31 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 32 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 33 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 34 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 35 80) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 36 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 37 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 37 79) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 38 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 39 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 39 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 40 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 41 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 41 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 42 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 43 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 43 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 44 75) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 45 75) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 45 75) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 46 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 47 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 48 78) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 49 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 50 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 50 77) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 51 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 52 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 52 76) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 53 75) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 54 75) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 54 75) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 55 74) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 56 74) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 56 74) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 57 75) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 58 74) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 59 74) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 59 74) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 60 73) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 61 73) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 61 73) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 62 72) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 63 72) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 63 72) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 64 71) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 65 69) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect_normalized 0 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 3 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 4 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 5 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 6 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 6 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 7 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 8 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 8 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 9 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 10 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 11 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 11 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 12 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 13 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 14 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 15 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 16 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 17 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 18 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 19 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 19 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 20 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 21 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 22 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 23 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 24 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 25 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 26 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 28 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 29 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 30 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 31 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 32 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 33 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 33 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 34 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 35 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 35 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 36 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 37 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 38 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 38 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 39 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 40 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 40 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 41 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 42 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 42 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 43 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 44 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 45 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 46 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 46 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 47 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 48 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 48 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 49 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 50 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 50 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 51 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 52 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 53 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 54 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 55 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 56 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 56 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 57 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 58 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 58 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 59 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect_normalized 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_packets_downRect 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_packets_downRect 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_packets_downRect 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_packets_downRect 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_packets_downRect 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_packets_downRect 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_packets_downRect 66) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (H_at_packets_downRect 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 0 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 3 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 66) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 5 67) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 6 66) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 7 66) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 7 66) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 8 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 9 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 9 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 10 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 11 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 11 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 12 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 13 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 14 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 15 65) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 16 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 17 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 17 64) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 18 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 19 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 19 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 20 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 21 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 22 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 23 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 24 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 26 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 27 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 28 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 29 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 29 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 30 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 31 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 31 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 32 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 33 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 33 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 34 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 35 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 36 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 37 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 38 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 38 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 39 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 40 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 40 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 41 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 42 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 42 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 43 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 44 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 45 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 46 63) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 47 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 48 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 48 62) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 49 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 50 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 50 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 51 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 52 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 52 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 53 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 54 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 54 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 55 58) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 56 58) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 56 58) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 57 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 58 60) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 59 61) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (D_at_column_downRect 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 59) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 58) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 58) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 58) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 3 57) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 4 57) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 57) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 5 56) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 6 56) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 6 56) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 7 57) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 8 56) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 9 56) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 9 56) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 10 55) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 11 55) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 11 55) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 12 54) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 13 54) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 54) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 14 53) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 15 51) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 15 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 15 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 15 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 16 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 17 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 17 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 18 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 19 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 19 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 20 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 21 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 22 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 23 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 24 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 25 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 26 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 26 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 27 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 28 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 28 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 29 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 30 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 31 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 32 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 33 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 34 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 34 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 35 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 36 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 36 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 37 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 38 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 38 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 39 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 40 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 40 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 41 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 42 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 43 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 44 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 45 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 46 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (D_at_column_downRect 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 3 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 4 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 5 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 5 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 6 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 7 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 7 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 8 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 9 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 9 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 10 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 11 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 12 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 13 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 14 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 15 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 15 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 16 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 17 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 17 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 18 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 19 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 20 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 22 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 23 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 24 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 25 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 26 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 27 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 28 44) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 29 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 30 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 31 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 32 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 33 49) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 34 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 35 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 35 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 36 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 37 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 37 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 38 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 39 49) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 40 50) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 41 49) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 42 49) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 42 49) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 43 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 44 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 44 48) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 45 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect_normalized 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_packets_downRect 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (H_at_packets_downRect 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 0 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 1 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 47) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 3 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 4 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 46) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 5 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 6 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 6 45) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 7 44) _).
  exact (X_dollar_column_downRect 8 44).
  }
  unfold y_event111_edge_stream; exact Hrect.
Qed.

Lemma y_event111_suffix_quadRect:
  quadRect tm (dollar_packets 111)
    (y_event111_suffix_word *> y_event111_edge_side).
Proof.
  eapply InfiniteRectInternal.downRect_quadRect_concat.
  - exact y_event111_suffix_downRect.
  - exact y_event111_edge_quadRect.
Qed.

Definition y_event111_config :=
  y_cut_left O O {{{ (hashR,R) }}}
    (y_event111_suffix_word *> y_event111_edge_side).

Lemma y_init_event111:
  c0 -[tm]->* y_event111_config.
Proof.
  eapply without_counter with (n:=147*(10^6)+268065).
  eapply multistep_c'_spec.
  native_check_eq.
Qed.

Theorem nonhalt:
  ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact y_init_event111.
  - unfold y_event111_config.
    eapply quadRect_nonhalt.
    + exact y_event111_suffix_quadRect.
    + exact y_cut_left_realizes.
Qed.
