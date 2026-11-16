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

Definition tm := Eval compute in (TM_from_str "1RB0LB_1RC1LB_0LA1RD_1RE0RA_0RF---_1LA0RF").

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6);
    [vm_compute; reflexivity | st; reflexivity]).

(* Directed heads and stationary column words from TM4x1.txt. *)
Notation hashR := (F,<[0]).
Notation hashL := (B,[1]).
Notation atSignalR := (F,<[0;0;0]).
Notation atSignalL := (B,[1;1;1;1;0;0;1;1]).
Notation dollarR := (A,<[1;1;0]).
Notation dollarL := (B,[1;1;0;0;1;1;0;0]).
Notation hash := [(hashR,hashL)].
Notation atSignal := [(atSignalR,atSignalL)].
Notation dollar := [(dollarR,dollarL)].

Notation cellX := [1;1;1;0;0;1;1].
Notation cellY := [1;1;1;0;0;0;0].
Notation cellH := [1;0].
Notation cellD := [1;0;0;1;1;0;0].
Notation cellP := [1;1].
Notation cellQ := [0;0].


(* One-column forms used by [downRect].  The width is the uniform positive
   progress bound; each certificate is checked against the original TM. *)
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

(* Complete ordinary-column transformations: a finite phase prefix followed
   by one of the four coinductive packet tails above.  These are precisely
   the four shapes produced by the symbolic X/Y column executor. *)
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

(* Initial cuts also contain a few transient D/P columns.  These lemmas
   consume their finite prefix and then reuse the same four packet tails as
   the periodic X/Y columns. *)
Lemma D_dollar_column_downRect (m:nat):
  downRect tm
    ((hash^^(S m)) *> dollar *>
      dollar_packets (S (S (S (S m)))))
    (dollar_packets m) cellD 1.
Proof.
  rewrite lpow_S, Str_app_assoc.
  change (downRect tm
    (hash *> ((hash^^m) *> dollar *>
      dollar_packets (S (S (S (S m))))))
    ([] *> dollar_packets m) cellD 1).
  eapply segRLs_n_downRect_trans.
  - exact hash_D_n.
  - pose proof (Y_dollar_column_downRect_normalized 0 m) as H.
    cbn [lpow] in H; exact H.
Qed.



Definition x_edge_groups : list edge_group_text := [
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "@#####" "X" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "##@#####" "XXXX" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#$##" "Y" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#$##" "Y" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "###$######" "Y"
    "1110011101001001001111";
  mk_edge_group_text "1110011101001001001111" "#####" "X"
    "1110011101001111110011101";
  mk_edge_group_text "1110011101001111110011101" "#@#######" "X"
    "11100111010000010010011101";
  mk_edge_group_text "11100111010000010010011101" "###@#" "XX"
    "111001111";
  mk_edge_group_text "111001111" "##" "X" "1110011";
  mk_edge_group_text "1110011" "#####" "X" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111";
  mk_edge_group_text "111001110101111" "##" "X" "11100001";
  mk_edge_group_text "11100001" "##@#####" "XXXX" "11100001";
  mk_edge_group_text "11100001" "####" "Y" "11100111011";
  mk_edge_group_text "11100111011" "#####" "X" "111001110101111"
].

Definition x_edge_group_sound :=
  edge_group_sound tm hash atSignal dollar cellX cellY.


Lemma x_edge_groups_sound:
  Forall x_edge_group_sound x_edge_groups.
Proof.
  unfold x_edge_groups.
  repeat (apply Forall_cons; [
    unfold x_edge_group_sound,edge_group_sound;
    cbn [signal_word_of_string bit_word_of_string column_word_of_string];
    esc|]).
  apply Forall_nil.
Qed.

Definition x_edge_phases : list edge_phase_text := [
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "#########@" PacketAt 21) (mk_packet_stream_text "#######@" PacketAt 21)
    (mk_packet_stream_text "########@" PacketAt 22);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "########@" PacketAt 22) (mk_packet_stream_text "####@" PacketAt 22)
    (mk_packet_stream_text "#####$" PacketDollar 21);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "#####$" PacketDollar 21) (mk_packet_stream_text "$" PacketDollar 21)
    (mk_packet_stream_text "@" PacketAt 20);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "@#####" "X" "11100111011")
    (mk_packet_stream_text "@" PacketAt 20) (mk_packet_stream_text "###############@" PacketAt 21)
    (mk_packet_stream_text "################@" PacketAt 22);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "################@" PacketAt 22) (mk_packet_stream_text "###########@" PacketAt 22)
    (mk_packet_stream_text "############@" PacketAt 23);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "############@" PacketAt 23) (mk_packet_stream_text "##########@" PacketAt 23)
    (mk_packet_stream_text "###########@" PacketAt 24);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "###########@" PacketAt 24) (mk_packet_stream_text "#######@" PacketAt 24)
    (mk_packet_stream_text "########$" PacketDollar 23);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "########$" PacketDollar 23) (mk_packet_stream_text "###$" PacketDollar 23)
    (mk_packet_stream_text "###@" PacketAt 22);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "###@" PacketAt 22) (mk_packet_stream_text "#@" PacketAt 22)
    (mk_packet_stream_text "##@" PacketAt 23);
  mk_edge_phase_text (mk_edge_group_text "11100001" "##@#####" "XXXX" "11100001")
    (mk_packet_stream_text "##@" PacketAt 23) (mk_packet_stream_text "##################@" PacketAt 24)
    (mk_packet_stream_text "######################@" PacketAt 28);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "######################@" PacketAt 28) (mk_packet_stream_text "##################@" PacketAt 28)
    (mk_packet_stream_text "###################$" PacketDollar 27);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "###################$" PacketDollar 27) (mk_packet_stream_text "##############$" PacketDollar 27)
    (mk_packet_stream_text "##############@" PacketAt 26);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "##############@" PacketAt 26) (mk_packet_stream_text "############@" PacketAt 26)
    (mk_packet_stream_text "#############@" PacketAt 27);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "#############@" PacketAt 27) (mk_packet_stream_text "#########@" PacketAt 27)
    (mk_packet_stream_text "##########$" PacketDollar 26);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "##########$" PacketDollar 26) (mk_packet_stream_text "#####$" PacketDollar 26)
    (mk_packet_stream_text "#####@" PacketAt 25);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "#####@" PacketAt 25) (mk_packet_stream_text "###@" PacketAt 25)
    (mk_packet_stream_text "####@" PacketAt 26);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "####@" PacketAt 26) (mk_packet_stream_text "@" PacketAt 26)
    (mk_packet_stream_text "#$" PacketDollar 25);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#$##" "Y" "11100001")
    (mk_packet_stream_text "#$" PacketDollar 25) (mk_packet_stream_text "#######################$" PacketDollar 26)
    (mk_packet_stream_text "#" PacketDollar 22);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "#" PacketDollar 22) (mk_packet_stream_text "###################$" PacketDollar 23)
    (mk_packet_stream_text "" PacketDollar 19);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "" PacketDollar 19) (mk_packet_stream_text "##############$" PacketDollar 20)
    (mk_packet_stream_text "##############@" PacketAt 19);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "##############@" PacketAt 19) (mk_packet_stream_text "############@" PacketAt 19)
    (mk_packet_stream_text "#############@" PacketAt 20);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "#############@" PacketAt 20) (mk_packet_stream_text "#########@" PacketAt 20)
    (mk_packet_stream_text "##########$" PacketDollar 19);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "##########$" PacketDollar 19) (mk_packet_stream_text "#####$" PacketDollar 19)
    (mk_packet_stream_text "#####@" PacketAt 18);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "#####@" PacketAt 18) (mk_packet_stream_text "###@" PacketAt 18)
    (mk_packet_stream_text "####@" PacketAt 19);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "####@" PacketAt 19) (mk_packet_stream_text "@" PacketAt 19)
    (mk_packet_stream_text "#$" PacketDollar 18);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#$##" "Y" "11100001")
    (mk_packet_stream_text "#$" PacketDollar 18) (mk_packet_stream_text "################$" PacketDollar 19)
    (mk_packet_stream_text "#" PacketDollar 15);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "#" PacketDollar 15) (mk_packet_stream_text "############$" PacketDollar 16)
    (mk_packet_stream_text "" PacketDollar 12);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "" PacketDollar 12) (mk_packet_stream_text "#######$" PacketDollar 13)
    (mk_packet_stream_text "#######@" PacketAt 12);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "#######@" PacketAt 12) (mk_packet_stream_text "#####@" PacketAt 12)
    (mk_packet_stream_text "######@" PacketAt 13);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "######@" PacketAt 13) (mk_packet_stream_text "##@" PacketAt 13)
    (mk_packet_stream_text "###$" PacketDollar 12);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "###$######" "Y" "1110011101001001001111")
    (mk_packet_stream_text "###$" PacketDollar 12) (mk_packet_stream_text "######$" PacketDollar 13)
    (mk_packet_stream_text "######$" PacketDollar 10);
  mk_edge_phase_text (mk_edge_group_text "1110011101001001001111" "#####" "X" "1110011101001111110011101")
    (mk_packet_stream_text "######$" PacketDollar 10) (mk_packet_stream_text "#$" PacketDollar 10)
    (mk_packet_stream_text "#@" PacketAt 9);
  mk_edge_phase_text (mk_edge_group_text "1110011101001111110011101" "#@#######" "X" "11100111010000010010011101")
    (mk_packet_stream_text "#@" PacketAt 9) (mk_packet_stream_text "##@" PacketAt 10)
    (mk_packet_stream_text "###@" PacketAt 11);
  mk_edge_phase_text (mk_edge_group_text "11100111010000010010011101" "###@#" "XX" "111001111")
    (mk_packet_stream_text "###@" PacketAt 11) (mk_packet_stream_text "##########@" PacketAt 12)
    (mk_packet_stream_text "############@" PacketAt 14);
  mk_edge_phase_text (mk_edge_group_text "111001111" "##" "X" "1110011")
    (mk_packet_stream_text "############@" PacketAt 14) (mk_packet_stream_text "##########@" PacketAt 14)
    (mk_packet_stream_text "###########@" PacketAt 15);
  mk_edge_phase_text (mk_edge_group_text "1110011" "#####" "X" "11100111011")
    (mk_packet_stream_text "###########@" PacketAt 15) (mk_packet_stream_text "######@" PacketAt 15)
    (mk_packet_stream_text "#######@" PacketAt 16);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "#######@" PacketAt 16) (mk_packet_stream_text "##@" PacketAt 16)
    (mk_packet_stream_text "###@" PacketAt 17);
  mk_edge_phase_text (mk_edge_group_text "111001110101111" "##" "X" "11100001")
    (mk_packet_stream_text "###@" PacketAt 17) (mk_packet_stream_text "#@" PacketAt 17)
    (mk_packet_stream_text "##@" PacketAt 18);
  mk_edge_phase_text (mk_edge_group_text "11100001" "##@#####" "XXXX" "11100001")
    (mk_packet_stream_text "##@" PacketAt 18) (mk_packet_stream_text "#############@" PacketAt 19)
    (mk_packet_stream_text "#################@" PacketAt 23);
  mk_edge_phase_text (mk_edge_group_text "11100001" "####" "Y" "11100111011")
    (mk_packet_stream_text "#################@" PacketAt 23) (mk_packet_stream_text "#############@" PacketAt 23)
    (mk_packet_stream_text "##############$" PacketDollar 22);
  mk_edge_phase_text (mk_edge_group_text "11100111011" "#####" "X" "111001110101111")
    (mk_packet_stream_text "##############$" PacketDollar 22) (mk_packet_stream_text "#########$" PacketDollar 22)
    (mk_packet_stream_text "#########@" PacketAt 21)

].


Lemma x_edge_phase_groups:
  map edge_phase_group x_edge_phases = x_edge_groups.
Proof. vm_compute; reflexivity. Qed.


Lemma x_edge_phase_consumes:
  Forall (fun p =>
    packet_stream_text_consume
      (edge_group_consume (edge_phase_group p))
      (edge_phase_stream p) = Some (edge_phase_tail p))
    x_edge_phases.
Proof. vm_compute; repeat constructor. Qed.

Definition x_phase_stream (d:packet_stream_text) :
    Stream (DH0*DH0) :=
  stream_of_text (hashR,hashL) (atSignalR,atSignalL)
    (dollarR,dollarL) d.

Definition x_column_flows : list column_flow_text := [
  mk_column_flow_text ColumnX (mk_packet_stream_text "#########$" PacketDollar 22) (mk_packet_stream_text "#########@" PacketAt 21);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######@" PacketAt 21) (mk_packet_stream_text "########@" PacketAt 22);
  mk_column_flow_text ColumnY (mk_packet_stream_text "####@" PacketAt 22) (mk_packet_stream_text "#####$" PacketDollar 21);
  mk_column_flow_text ColumnX (mk_packet_stream_text "$" PacketDollar 21) (mk_packet_stream_text "@" PacketAt 20);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############@" PacketAt 21) (mk_packet_stream_text "################@" PacketAt 22);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########@" PacketAt 22) (mk_packet_stream_text "############@" PacketAt 23);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########@" PacketAt 23) (mk_packet_stream_text "###########@" PacketAt 24);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#######@" PacketAt 24) (mk_packet_stream_text "########$" PacketDollar 23);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###$" PacketDollar 23) (mk_packet_stream_text "###@" PacketAt 22);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#@" PacketAt 22) (mk_packet_stream_text "##@" PacketAt 23);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##################@" PacketAt 24) (mk_packet_stream_text "###################@" PacketAt 25);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###################@" PacketAt 25) (mk_packet_stream_text "####################@" PacketAt 26);
  mk_column_flow_text ColumnX (mk_packet_stream_text "####################@" PacketAt 26) (mk_packet_stream_text "#####################@" PacketAt 27);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####################@" PacketAt 27) (mk_packet_stream_text "######################@" PacketAt 28);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##################@" PacketAt 28) (mk_packet_stream_text "###################$" PacketDollar 27);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##############$" PacketDollar 27) (mk_packet_stream_text "##############@" PacketAt 26);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############@" PacketAt 26) (mk_packet_stream_text "#############@" PacketAt 27);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#########@" PacketAt 27) (mk_packet_stream_text "##########$" PacketDollar 26);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####$" PacketDollar 26) (mk_packet_stream_text "#####@" PacketAt 25);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###@" PacketAt 25) (mk_packet_stream_text "####@" PacketAt 26);
  mk_column_flow_text ColumnY (mk_packet_stream_text "@" PacketAt 26) (mk_packet_stream_text "#$" PacketDollar 25);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#######################$" PacketDollar 26) (mk_packet_stream_text "#" PacketDollar 22);
  mk_column_flow_text ColumnY (mk_packet_stream_text "###################$" PacketDollar 23) (mk_packet_stream_text "" PacketDollar 19);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##############$" PacketDollar 20) (mk_packet_stream_text "##############@" PacketAt 19);
  mk_column_flow_text ColumnX (mk_packet_stream_text "############@" PacketAt 19) (mk_packet_stream_text "#############@" PacketAt 20);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#########@" PacketAt 20) (mk_packet_stream_text "##########$" PacketDollar 19);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####$" PacketDollar 19) (mk_packet_stream_text "#####@" PacketAt 18);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###@" PacketAt 18) (mk_packet_stream_text "####@" PacketAt 19);
  mk_column_flow_text ColumnY (mk_packet_stream_text "@" PacketAt 19) (mk_packet_stream_text "#$" PacketDollar 18);
  mk_column_flow_text ColumnY (mk_packet_stream_text "################$" PacketDollar 19) (mk_packet_stream_text "#" PacketDollar 15);
  mk_column_flow_text ColumnY (mk_packet_stream_text "############$" PacketDollar 16) (mk_packet_stream_text "" PacketDollar 12);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#######$" PacketDollar 13) (mk_packet_stream_text "#######@" PacketAt 12);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#####@" PacketAt 12) (mk_packet_stream_text "######@" PacketAt 13);
  mk_column_flow_text ColumnY (mk_packet_stream_text "##@" PacketAt 13) (mk_packet_stream_text "###$" PacketDollar 12);
  mk_column_flow_text ColumnY (mk_packet_stream_text "######$" PacketDollar 13) (mk_packet_stream_text "######$" PacketDollar 10);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#$" PacketDollar 10) (mk_packet_stream_text "#@" PacketAt 9);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##@" PacketAt 10) (mk_packet_stream_text "###@" PacketAt 11);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########@" PacketAt 12) (mk_packet_stream_text "###########@" PacketAt 13);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###########@" PacketAt 13) (mk_packet_stream_text "############@" PacketAt 14);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##########@" PacketAt 14) (mk_packet_stream_text "###########@" PacketAt 15);
  mk_column_flow_text ColumnX (mk_packet_stream_text "######@" PacketAt 15) (mk_packet_stream_text "#######@" PacketAt 16);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##@" PacketAt 16) (mk_packet_stream_text "###@" PacketAt 17);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#@" PacketAt 17) (mk_packet_stream_text "##@" PacketAt 18);
  mk_column_flow_text ColumnX (mk_packet_stream_text "#############@" PacketAt 19) (mk_packet_stream_text "##############@" PacketAt 20);
  mk_column_flow_text ColumnX (mk_packet_stream_text "##############@" PacketAt 20) (mk_packet_stream_text "###############@" PacketAt 21);
  mk_column_flow_text ColumnX (mk_packet_stream_text "###############@" PacketAt 21) (mk_packet_stream_text "################@" PacketAt 22);
  mk_column_flow_text ColumnX (mk_packet_stream_text "################@" PacketAt 22) (mk_packet_stream_text "#################@" PacketAt 23);
  mk_column_flow_text ColumnY (mk_packet_stream_text "#############@" PacketAt 23) (mk_packet_stream_text "##############$" PacketDollar 22)
].

Definition x_column_flow_sound (f:column_flow_text) : Prop :=
  downRect tm (x_phase_stream (column_flow_input f))
    (x_phase_stream (column_flow_output f))
    (match column_flow_symbol f with ColumnX => cellX | ColumnY => cellY end) 1.


Ltac x_flow cert :=
  unfold x_column_flow_sound, x_phase_stream;
  cbn [stream_of_text signal_word_of_string]; exact cert.

Lemma x_column_flows_sound:
  Forall x_column_flow_sound x_column_flows.
Proof.
  unfold x_column_flows.
  apply Forall_cons; [x_flow (X_dollar_column_downRect 9 21)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 7 21)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 4 20)|].
  apply Forall_cons; [x_flow (X_dollar_column_downRect 0 20)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 15 21)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 11 22)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 10 23)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 7 22)|].
  apply Forall_cons; [x_flow (X_dollar_column_downRect 3 22)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 1 22)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 18 24)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 19 25)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 20 26)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 21 27)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 18 26)|].
  apply Forall_cons; [x_flow (X_dollar_column_downRect 14 26)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 12 26)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 9 25)|].
  apply Forall_cons; [x_flow (X_dollar_column_downRect 5 25)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 3 25)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 0 24)|].
  apply Forall_cons; [x_flow (Y_dollar_column_downRect_normalized 1 22)|].
  apply Forall_cons; [x_flow (Y_dollar_column_downRect_normalized 0 19)|].
  apply Forall_cons; [x_flow (X_dollar_column_downRect 14 19)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 12 19)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 9 18)|].
  apply Forall_cons; [x_flow (X_dollar_column_downRect 5 18)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 3 18)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 0 17)|].
  apply Forall_cons; [x_flow (Y_dollar_column_downRect_normalized 1 15)|].
  apply Forall_cons; [x_flow (Y_dollar_column_downRect_normalized 0 12)|].
  apply Forall_cons; [x_flow (X_dollar_column_downRect 7 12)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 5 12)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 2 11)|].
  apply Forall_cons; [x_flow (Y_dollar_column_downRect 6 10)|].
  apply Forall_cons; [x_flow (X_dollar_column_downRect 1 9)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 2 10)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 10 12)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 11 13)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 10 14)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 6 15)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 2 16)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 1 17)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 13 19)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 14 20)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 15 21)|].
  apply Forall_cons; [x_flow (X_at_column_downRect 16 22)|].
  apply Forall_cons; [x_flow (Y_at_column_downRect 13 21)|].
  apply Forall_nil.
Qed.

Definition x_phase_columns : list (list column_flow_text) :=
  partition_phase_columns x_edge_phases
    (tl x_column_flows ++
      [hd default_column_flow x_column_flows]).


Lemma x_phase_columns_match:
  Forall2 phase_columns_match x_edge_phases x_phase_columns.
Proof. vm_compute; repeat constructor; congruence. Qed.

Lemma x_rotated_column_flows_sound:
  Forall x_column_flow_sound
    (tl x_column_flows ++
      [hd default_column_flow x_column_flows]).
Proof.
  apply Forall_rotate_local.
  - vm_compute; discriminate.
  - exact x_column_flows_sound.
Qed.

Lemma x_phase_columns_flows_sound:
  Forall (Forall x_column_flow_sound) x_phase_columns.
Proof.
  unfold x_phase_columns.
  apply partition_phase_columns_Forall.
  exact x_rotated_column_flows_sound.
Qed.

Definition x_column_symbol_word (s:column_symbol) : list Sym :=
  match s with ColumnX => cellX | ColumnY => cellY end.

Fixpoint x_column_flow_word (fs:list column_flow_text) : list Sym :=
  match fs with
  | [] => []
  | f::fs' => x_column_symbol_word (column_flow_symbol f) ++
      x_column_flow_word fs'
  end.

Fixpoint x_column_symbols_word (ss:list column_symbol) : list Sym :=
  match ss with
  | [] => []
  | s::ss' => x_column_symbol_word s ++
      x_column_symbols_word ss'
  end.

Lemma x_column_flow_word_symbols fs:
  x_column_flow_word fs =
    x_column_symbols_word (map column_flow_symbol fs).
Proof. induction fs; cbn; rewrite ?IHfs; reflexivity. Qed.

Lemma x_column_word_of_string_symbols s:
  column_word_of_string cellX cellY s =
    x_column_symbols_word (column_symbols_of_string s).
Proof.
  induction s as [|a s IH]; cbn
    [column_word_of_string column_symbols_of_string
      x_column_symbols_word x_column_symbol_word].
  - reflexivity.
  - destruct (Nat.eqb (nat_of_ascii a) 88); rewrite IH; reflexivity.
Qed.

Lemma x_column_flow_chain_downRect fs:
  fs <> [] ->
  Forall x_column_flow_sound fs ->
  column_flows_linked fs ->
  downRect tm
    (x_phase_stream (column_flow_input
      (hd default_column_flow fs)))
    (x_phase_stream (column_flow_output
      (last fs default_column_flow)))
    (x_column_flow_word fs) (length fs).
Proof.
  induction fs as [|f fs IH]; intros Hne Hsound Hlinked.
  - contradiction.
  - destruct fs as [|g fs].
    + inversion Hsound; subst.
      unfold x_column_flow_sound in H1.
      cbn [x_column_flow_word x_column_symbol_word hd last].
      rewrite app_nil_r.
      change (downRect tm
        (x_phase_stream (column_flow_input f))
        (x_phase_stream (column_flow_output f))
        (x_column_symbol_word (column_flow_symbol f)) 1).
      unfold x_column_symbol_word.
      exact H1.
    + inversion Hsound as [|? ? Hf Htail]; subst.
      cbn [column_flows_linked] in Hlinked.
      destruct Hlinked as [Hfg Hlinked].
      specialize (IH ltac:(discriminate) Htail Hlinked).
      unfold x_column_flow_sound in Hf.
      rewrite Hfg in Hf.
      pose proof (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
        Hf IH) as Hcat.
      cbn [x_column_flow_word x_column_symbol_word hd last] in *.
      exact Hcat.
Qed.

Lemma x_phase_columns_downRect p fs:
  phase_columns_match p fs ->
  Forall x_column_flow_sound fs ->
  downRect tm (x_phase_stream (edge_phase_tail p))
    (x_phase_stream (edge_phase_next_stream p))
    (column_word_of_string cellX cellY
      (edge_group_emit (edge_phase_group p)))
    (length fs).
Proof.
  intros [Hne [Hin [Hout [Hlinked Hsymbols]]]] Hsound.
  pose proof (x_column_flow_chain_downRect fs Hne Hsound Hlinked)
    as Hrect.
  rewrite Hin, Hout in Hrect.
  rewrite x_column_flow_word_symbols, Hsymbols,
    <- x_column_word_of_string_symbols in Hrect.
  exact Hrect.
Qed.

Lemma x_edge_phase_downRects:
  Forall2 (fun p fs =>
    downRect tm (x_phase_stream (edge_phase_tail p))
      (x_phase_stream (edge_phase_next_stream p))
      (column_word_of_string cellX cellY
        (edge_group_emit (edge_phase_group p)))
      (length fs))
    x_edge_phases x_phase_columns.
Proof.
  pose proof x_phase_columns_match as Hmatch.
  pose proof x_phase_columns_flows_sound as Hsound.
  induction Hmatch; inversion Hsound; subst; constructor.
  - eapply x_phase_columns_downRect; eauto.
  - apply IHHmatch; assumption.
Qed.

Definition x_next_phases : list edge_phase_text :=
  tl x_edge_phases ++ [hd
    (mk_edge_phase_text
      (mk_edge_group_text "" "" "" "")
      (mk_packet_stream_text "" PacketAt 0)
      (mk_packet_stream_text "" PacketAt 0)
      (mk_packet_stream_text "" PacketAt 0))
    x_edge_phases].

Definition x_phase_next_match (p q:edge_phase_text) : Prop :=
  edge_group_after (edge_phase_group p) =
    edge_group_before (edge_phase_group q) /\
  edge_phase_next_stream p = edge_phase_stream q.

Lemma x_phase_next_matches:
  Forall2 x_phase_next_match x_edge_phases x_next_phases.
Proof. vm_compute; repeat constructor. Qed.

Lemma x_next_phase_in q:
  In q x_next_phases -> In q x_edge_phases.
Proof. vm_compute; intuition congruence. Qed.

Lemma x_phase_columns_positive:
  Forall (fun fs => O < length fs) x_phase_columns.
Proof. vm_compute; repeat constructor; lia. Qed.

Lemma x_edge_phases_emit_nonempty:
  Forall (fun p =>
    column_word_of_string cellX cellY
      (edge_group_emit (edge_phase_group p)) <> [])
    x_edge_phases.
Proof. vm_compute; repeat constructor; discriminate. Qed.

Definition x_cycle (L:Stream (DH0*DH0)) (top:side) : Prop :=
  exists p, In p x_edge_phases /\
    L = x_phase_stream (edge_phase_stream p) /\
    top = bit_word_of_string
      (edge_group_before (edge_phase_group p)) *> 0inf.

Lemma x_cycle_dynamic_step L top:
  x_cycle L top -> dynamic_side_step tm x_cycle L top.
Proof.
  intros [p [Hp [HL Htop]]].
  pose proof x_edge_phase_consumes as Hconsume.
  rewrite Forall_forall in Hconsume; specialize (Hconsume p Hp).
  assert (Hgp: In (edge_phase_group p) x_edge_groups).
  { rewrite <- x_edge_phase_groups. apply in_map. exact Hp. }
  pose proof x_edge_groups_sound as Hedge.
  rewrite Forall_forall in Hedge;
    specialize (Hedge (edge_phase_group p) Hgp).
  destruct (Forall2_In_left_exists _ _ _ p
    x_edge_phase_downRects Hp) as [fs [Hfs Hrect]].
  pose proof x_phase_columns_positive as Hwidth.
  rewrite Forall_forall in Hwidth; specialize (Hwidth fs Hfs).
  pose proof x_edge_phases_emit_nonempty as Hemit.
  rewrite Forall_forall in Hemit; specialize (Hemit p Hp).
  destruct (Forall2_In_left_exists _ _ _ p
    x_phase_next_matches Hp) as [q [Hq Hnext]].
  destruct Hnext as [Hedge_next Hstream_next].
  exists
    (signal_word_of_string hash atSignal dollar
      (edge_group_consume (edge_phase_group p))),
    (x_phase_stream (edge_phase_tail p)),
    (x_phase_stream (edge_phase_next_stream p)),
    (bit_word_of_string (edge_group_after (edge_phase_group p)) *> 0inf),
    (column_word_of_string cellX cellY
      (edge_group_emit (edge_phase_group p))),
    (length fs).
  split; [exact Hwidth|].
  split; [exact Hemit|].
  split.
  - rewrite HL.
    unfold x_phase_stream.
    eapply packet_stream_text_consume_sound; exact Hconsume.
  - split.
    + rewrite Htop. exact Hedge.
    + split; [exact Hrect|].
      exists q. split.
      * apply x_next_phase_in; exact Hq.
      * split.
        -- rewrite Hstream_next. reflexivity.
        -- rewrite <- Hedge_next. reflexivity.
Qed.

Lemma x_cycle_quadRect L top:
  x_cycle L top -> quadRect tm L top.
Proof.
  intro Hcycle.
  apply dynamic_side_unbounded with (P:=x_cycle).
  - exact x_cycle_dynamic_step.
  - exact Hcycle.
Qed.

Definition x_anchor_descriptor : packet_stream_text :=
  mk_packet_stream_text "##############$" PacketDollar 22.

Definition x_anchor_stream : Stream (DH0*DH0) :=
  x_phase_stream x_anchor_descriptor.

Definition x_anchor_side : side :=
  bit_word_of_string "11100111011" *> 0inf.

Lemma x_anchor_cycle:
  x_cycle x_anchor_stream x_anchor_side.
Proof.
  unfold x_cycle, x_anchor_stream, x_anchor_side.
  exists (last x_edge_phases
    (mk_edge_phase_text
      (mk_edge_group_text "" "" "" "")
      (mk_packet_stream_text "" PacketAt 0)
      (mk_packet_stream_text "" PacketAt 0)
      (mk_packet_stream_text "" PacketAt 0))).
  split.
  - vm_compute; intuition congruence.
  - split; reflexivity.
Qed.

Lemma x_anchor_quadRect:
  quadRect tm x_anchor_stream x_anchor_side.
Proof. apply x_cycle_quadRect, x_anchor_cycle. Qed.

(* The acyclic entrance to the periodic dotted column.  Each step stops at
   the first nonempty emission; the emitted ordinary columns are then moved
   by [downRect], and the remaining suffix is again a dotted column. *)
Definition x_preedge_descriptor : packet_stream_text :=
  mk_packet_stream_text "###############@" PacketAt 19.

Definition x_preedge_stream : Stream (DH0*DH0) :=
  x_phase_stream x_preedge_descriptor.

Definition x_preedge_side : side :=
  bit_word_of_string "1110011100001" *> 0inf.

Definition x_after_four_X_descriptor : packet_stream_text :=
  mk_packet_stream_text "#################@" PacketAt 23.

Definition x_after_four_X_stream : Stream (DH0*DH0) :=
  x_phase_stream x_after_four_X_descriptor.

Definition x_after_four_X_side : side :=
  bit_word_of_string "11100001" *> 0inf.

Lemma x_preedge_until_four_X:
  sideRLs tm (hash^^2) x_preedge_side
    ((cellX^^4) *> x_after_four_X_side).
Proof.
  unfold x_preedge_side, x_after_four_X_side.
  cbn [lpow bit_word_of_string]. esc.
Qed.

Lemma x_after_four_X_until_Y:
  sideRLs tm (hash^^4) x_after_four_X_side
    (cellY *> x_anchor_side).
Proof.
  unfold x_after_four_X_side, x_anchor_side.
  cbn [lpow bit_word_of_string]. esc.
Qed.

Lemma x_preedge_consume:
  packet_stream_text_consume "##" x_preedge_descriptor =
    Some (mk_packet_stream_text "#############@" PacketAt 19).
Proof. vm_compute; reflexivity. Qed.

Lemma x_after_four_X_consume:
  packet_stream_text_consume "####" x_after_four_X_descriptor =
    Some (mk_packet_stream_text "#############@" PacketAt 23).
Proof. vm_compute; reflexivity. Qed.

Lemma x_four_X_downRect:
  downRect tm
    (x_phase_stream
      (mk_packet_stream_text "#############@" PacketAt 19))
    x_after_four_X_stream (cellX^^4) 4.
Proof.
  pose proof (X_at_column_downRect 13 19) as H1.
  pose proof (X_at_column_downRect 14 20) as H2.
  pose proof (X_at_column_downRect 15 21) as H3.
  pose proof (X_at_column_downRect 16 22) as H4.
  pose proof (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    H1 H2) as H12.
  pose proof (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    H12 H3) as H123.
  pose proof (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    H123 H4) as H1234.
  unfold x_phase_stream, x_after_four_X_stream,
    x_after_four_X_descriptor.
  cbn [stream_of_text signal_word_of_string] in *.
  exact H1234.
Qed.

Lemma x_after_four_X_quadRect:
  quadRect tm x_after_four_X_stream x_after_four_X_side.
Proof.
  assert (Hsplit:
    x_after_four_X_stream =
      (hash^^4) *>
        x_phase_stream
          (mk_packet_stream_text "#############@" PacketAt 23)).
  {
    pose proof (packet_stream_text_consume_sound
      (hashR,hashL) (atSignalR,atSignalL) (dollarR,dollarL)
      "####" x_after_four_X_descriptor
      (mk_packet_stream_text "#############@" PacketAt 23)
      x_after_four_X_consume) as Hconsume.
    cbn [signal_word_of_string lpow] in Hconsume.
    exact Hconsume.
  }
  rewrite Hsplit.
  eapply sideRLs_downRect_quadRect with
    (w:=cellY) (width:=1%nat) (Ledge:=x_anchor_stream)
    (top':=x_anchor_side).
  - lia.
  - exact x_after_four_X_until_Y.
  - unfold x_phase_stream.
    cbn [stream_of_text signal_word_of_string].
    exact (Y_at_column_downRect 13 21).
  - exact x_anchor_quadRect.
Qed.

Lemma x_preedge_quadRect:
  quadRect tm x_preedge_stream x_preedge_side.
Proof.
  assert (Hsplit:
    x_preedge_stream =
      (hash^^2) *>
        x_phase_stream
          (mk_packet_stream_text "#############@" PacketAt 19)).
  {
    pose proof (packet_stream_text_consume_sound
      (hashR,hashL) (atSignalR,atSignalL) (dollarR,dollarL)
      "##" x_preedge_descriptor
      (mk_packet_stream_text "#############@" PacketAt 19)
      x_preedge_consume) as Hconsume.
    cbn [signal_word_of_string lpow] in Hconsume.
    exact Hconsume.
  }
  rewrite Hsplit.
  eapply sideRLs_downRect_quadRect with
    (w:=cellX^^4) (width:=4%nat) (Ledge:=x_after_four_X_stream)
    (top':=x_after_four_X_side).
  - lia.
  - exact x_preedge_until_four_X.
  - exact x_four_X_downRect.
  - exact x_after_four_X_quadRect.
Qed.

(* The 91 one-off ordinary columns to the left of the dotted pre-edge.
   Their order is the exact cut from the column analysis; the proof below
   composes the complete infinite input/output flow of every adjacent pair. *)
Definition x_initial_column_symbol_word
    (s:ordinary_column_symbol) : list Sym :=
  match s with
  | OrdinaryX => cellX | OrdinaryY => cellY | OrdinaryH => cellH
  | OrdinaryD => cellD | OrdinaryP => cellP | OrdinaryQ => cellQ
  end.

Definition x_initial_suffix_symbols : list ordinary_column_symbol := [
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryY; OrdinaryD; OrdinaryP;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryY;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY;
  OrdinaryP; OrdinaryX; OrdinaryY; OrdinaryY; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryY;
  OrdinaryY; OrdinaryX; OrdinaryX; OrdinaryY; OrdinaryY; OrdinaryX;
  OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX; OrdinaryX;
  OrdinaryX
].

Definition x_initial_suffix_word : list Sym :=
  fold_right (fun s w => x_initial_column_symbol_word s ++ w) []
    x_initial_suffix_symbols.

Definition x_initial_suffix_descriptor : packet_stream_text :=
  mk_packet_stream_text "###################$" PacketDollar 40.

Definition x_initial_suffix_stream : Stream (DH0*DH0) :=
  x_phase_stream x_initial_suffix_descriptor.


Lemma x_initial_suffix_downRect:
  downRect tm x_initial_suffix_stream x_preedge_stream
    x_initial_suffix_word 91.
Proof.
  assert (Hrect: downRect tm
    ((hash^^19) *> dollar *> dollar_packets 40)
    ((hash^^15) *> atSignal *> at_packets 19)
    x_initial_suffix_word 91).
  {
  unfold x_initial_suffix_word, x_initial_suffix_symbols,
    x_initial_column_symbol_word.
  cbn [fold_right].
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 19 39) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 19 39) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 20 38) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 21 38) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 38) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 22 39) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 23 40) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 24 39) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 25 39) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 39) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 26 40) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 41) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 28 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 29 43) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 30 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 31 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 31 42) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 32 41) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 33 41) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 33 41) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 34 40) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 35 38) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (D_dollar_column_downRect 34) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 33) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 33) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 32) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 32) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 32) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 3 31) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 4 29) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 4 26) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 4 25) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 25) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 5 24) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 6 22) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 6 21) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 6 21) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 7 22) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 8 23) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 9 24) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 10 25) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 11 26) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 12 27) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 28) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 14 29) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 15 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 16 31) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 17 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 18 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 18 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 19 29) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 20 29) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 20 29) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 21 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 22 31) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 23 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 24 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 24 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 25 31) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 26 32) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 27 33) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 28 34) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 29 33) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 30 33) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 30 33) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect_normalized 31) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (P_dollar_packets_downRect 31) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 0 31) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 1 30) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 2 28) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 2 25) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 2 24) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 2 24) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 3 23) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 4 23) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 4 23) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 5 22) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 6 20) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 6 17) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 6 16) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 6 16) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_at_column_downRect 7 15) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (Y_dollar_column_downRect 8 13) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_dollar_column_downRect 8 12) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 8 12) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 9 13) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 10 14) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 11 15) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 12 16) _).
  refine (InfiniteRectInternal.downRect_concat _ _ _ _ _ _ _ _
    (X_at_column_downRect 13 17) _).
  exact (X_at_column_downRect 14 18).
  }
  unfold x_initial_suffix_stream, x_initial_suffix_descriptor,
    x_preedge_stream, x_preedge_descriptor, x_phase_stream.
  cbn [stream_of_text signal_word_of_string] in *.
  exact Hrect.
Qed.

Lemma x_initial_suffix_quadRect:
  quadRect tm x_initial_suffix_stream
    (x_initial_suffix_word *> x_preedge_side).
Proof.
  eapply InfiniteRectInternal.downRect_quadRect_concat.
  - exact x_initial_suffix_downRect.
  - exact x_preedge_quadRect.
Qed.

Notation hashLR := [(hashL,hashR)].
Notation hashLdollarR := [(hashL,dollarR)].
Notation dollarLhR := [(dollarL,hashR)].

Definition x_initial_F (a b:nat) : side :=
  0inf
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1]
  <* <[1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1]
  <* <[1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1]
  <* <[1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1]
  <* <[1;1;0;1;1;1;1]^^a
  <* <[0;0]
  <* <[1;1;0;1;1;1;1]^^b
  <* <[0;0;1;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1]
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1].

Definition x_initial_G (a b:nat) : side :=
  0inf
  <* <[1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;0;1;1]
  <* <[1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1]
  <* <[1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1]
  <* <[1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;0;0;1;1;1]
  <* <[1;1]
  <* <[1;1;0;1;1;1;1]^^a
  <* <[0;0]
  <* <[1;1;0;1;1;1;1]^^b
  <* <[0;0;1;1;1;1;1].

Definition x_initial_cut_left : side := x_initial_F O 4.

(* The reset call crosses the cut twice.  Naming the concrete intermediate
   side keeps each symbolic-execution certificate at constant boundary size. *)
Definition x_initial_reset_mid : side :=
  0inf <* rev (bit_word_of_string
    "11011111101111110111111011111101111110111111011111101111110111111011110011011111101111110111111011111101111110111111011111101111110111111011111101111110111111011111101111110111111011111101111110111111011111101111110111111011110011111110111111011111101111110111111011110011111001111111011111101111110111111011111101111110111111011111101111110111111011111101111110111111011111101111").

Definition x_initial_post_dollar : side :=
  0inf <* rev (bit_word_of_string
    "110111111011111101111110111111011111101111110111111011111101111110111111011111101111001101111110111111011111101111110111111011111101111110111111011111101111110111111011111101111110111111011111101111110111111011111101111110111100111111101111110111111011111101111110111100111110011111110111111011111101111110111111011111101111110111111011111101111110111111011111101111110111111011110011111").

(* Exact two-parameter family reached after the transient dollar.  The marker
   [0011011] moves right while [a] grows and [b] shrinks. *)
Definition x_actual_cut (a b:nat) : side :=
  0inf
  <* rev (bit_word_of_string
    "110111111011111101111110111111011111101111110111111011111101111110111111011111101111")
  <* <[1;1;0;1;1;1;1]^^a
  <* <[0;0;1;1;0;1;1]
  <* <[1;1;1;1;0;1;1]^^b
  <* <[1;1;1;1;0;1;1]
  <* rev (bit_word_of_string
    "1100111111101111110111111011111101111110111100111110011111110111111011111101111110111111011111101111110111111011111101111110111111011111101111110111111011110011111").

Lemma x_initial_post_dollar_eq:
  x_initial_post_dollar = x_actual_cut O 18.
Proof. vm_compute. reflexivity. Qed.

Lemma x_initial_F_shift a b:
  sideRLs (flip tm) hashLR
    (x_initial_F a (1+b)) (x_initial_F (1+a) b).
Proof.
  unfold x_initial_F. es' a b.
Qed.

Lemma x_initial_G_shift a b:
  sideRLs (flip tm) hashLR
    (x_initial_G a (1+b)) (x_initial_G (1+a) b).
Proof.
  unfold x_initial_G. es' a b.
Qed.

Lemma x_initial_F_to_G:
  sideRLs (flip tm) hashLR
    (x_initial_F 4 O) (x_initial_G O 13).
Proof.
  unfold x_initial_F, x_initial_G. es'.
Qed.

Lemma x_initial_G_emit_dollar:
  sideRLs (flip tm) hashLdollarR
    (x_initial_G 13 O) x_initial_reset_mid.
Proof.
  unfold x_initial_G, x_initial_reset_mid.
  cbn [bit_word_of_string rev]. es'.
Qed.

Ltac es_v3_TL ::= constr:(10000).

Lemma x_initial_G_accept_dollar:
  sideRLs (flip tm) dollarLhR
    x_initial_reset_mid x_initial_post_dollar.
Proof.
  unfold x_initial_reset_mid, x_initial_post_dollar.
  cbn [bit_word_of_string rev]. es'.
Qed.

Lemma x_initial_G_enter_cycle:
  sideRLs (flip tm) (hashLdollarR ++ dollarLhR)
    (x_initial_G 13 O) x_initial_post_dollar.
Proof.
  eapply sideRLs_trans.
  - exact x_initial_G_emit_dollar.
  - exact x_initial_G_accept_dollar.
Qed.

Lemma x_initial_F_run a b:
  sideRLs (flip tm) (hashLR^^b)
    (x_initial_F a b) (x_initial_F (a+b) O).
Proof.
  revert a; induction b as [|b IH]; intro a.
  - cbn [lpow]. replace (a+0) with a by lia. constructor.
  - cbn [lpow]. replace (a+S b) with (1+a+b) by lia.
    eapply sideRLs_trans.
    + apply x_initial_F_shift.
    + apply IH.
Qed.

Lemma x_initial_G_run a b:
  sideRLs (flip tm) (hashLR^^b)
    (x_initial_G a b) (x_initial_G (a+b) O).
Proof.
  revert a; induction b as [|b IH]; intro a.
  - cbn [lpow]. replace (a+0) with a by lia. constructor.
  - cbn [lpow]. replace (a+S b) with (1+a+b) by lia.
    eapply sideRLs_trans.
    + apply x_initial_G_shift.
    + apply IH.
Qed.

Lemma x_initial_cut_signals:
  sideRLs (flip tm)
    ((hashLR^^18) ++ hashLdollarR ++ dollarLhR)
    x_initial_cut_left x_initial_post_dollar.
Proof.
  pose proof (x_initial_F_run O 4) as H0.
  pose proof (sideRLs_trans H0 x_initial_F_to_G) as H1.
  pose proof (x_initial_G_run O 13) as HG.
  pose proof (sideRLs_trans H1 HG) as H2.
  pose proof (sideRLs_trans H2 x_initial_G_enter_cycle) as H3.
  unfold x_initial_cut_left.
  replace ((((hashLR^^4) ++ hashLR) ++ (hashLR^^13)) ++
      (hashLdollarR ++ dollarLhR))
    with ((hashLR^^18) ++ hashLdollarR ++ dollarLhR) in H3
    by (vm_compute; reflexivity).
  exact H3.
Qed.

Ltac es_v3_TL ::= constr:(20000).

Lemma x_actual_shift a b:
  sideRLs (flip tm) hashLR
    (x_actual_cut a (1+b)) (x_actual_cut (1+a) b).
Proof.
  unfold x_actual_cut. cbn [bit_word_of_string rev]. es' a b.
Qed.

Lemma x_actual_reset a:
  sideRLs (flip tm)
    ((hashLR^^21) ++ hashLdollarR ++ dollarLhR)
    (x_actual_cut a O) (x_actual_cut O (1+a)).
Proof.
  unfold x_actual_cut. cbn [bit_word_of_string rev]. es' a.
Qed.

Definition x_actual_stream (a b:nat) : Stream (DH0*DH0) :=
  (hash^^(b+22)) *> dollar *> dollar_packets (a+b+23).

Lemma x_actual_stream_shift a b:
  x_actual_stream a (1+b) =
    hash *> x_actual_stream (1+a) b.
Proof.
  unfold x_actual_stream.
  replace (1+b+22) with (S (b+22)) by lia.
  rewrite lpow_S, Str_app_assoc.
  replace (a+(1+b)+23) with (1+a+b+23) by lia.
  reflexivity.
Qed.

Lemma x_actual_stream_new_packet a:
  x_actual_stream O (1+a) = dollar_packets (a+23).
Proof.
  unfold x_actual_stream.
  replace (1+a+22) with (a+23) by lia.
  replace (0+(1+a)+23) with (S (a+23)) by lia.
  rewrite <- Str_app_assoc.
  unfold dollar_packets.
  rewrite <- repeat_singleton_lpow.
  symmetry. apply growing_packets_unfold.
Qed.

Lemma x_actual_stream_reset a:
  x_actual_stream a O =
    ((hash^^22) ++ dollar) *> x_actual_stream O (1+a).
Proof.
  unfold x_actual_stream at 1.
  cbn [Nat.add]. rewrite x_actual_stream_new_packet.
  replace (a+0+23) with (a+23) by lia.
  rewrite Str_app_assoc. reflexivity.
Qed.

Lemma x_actual_stream_initial:
  x_actual_stream O 18 = dollar_packets 40.
Proof.
  unfold x_actual_stream. cbn [Nat.add].
  rewrite <- Str_app_assoc.
  unfold dollar_packets.
  rewrite <- repeat_singleton_lpow.
  symmetry. apply growing_packets_unfold.
Qed.

Inductive XActualState : DH0 -> Stream (DH0*DH0) -> side -> Prop :=
| XActual a b : XActualState hashR
    (x_actual_stream a b) (x_actual_cut a b).

Lemma x_actual_cut_realizes_general a0 b0:
  leftRealizes tm hashR (x_actual_stream a0 b0)
    (x_actual_cut a0 b0).
Proof.
  eapply leftRealizes_inf_concat with (P:=XActualState).
  - intros h0 L l Hstate. inversion Hstate as [a b]; subst.
    destruct b as [|b].
    + exists ((hash^^22)++dollar),
        (x_actual_stream O (1+a)), hashR,
        ((hashLR^^21)++hashLdollarR++dollarLhR),
        (x_actual_cut O (1+a)).
      split; [change (O<23); lia|].
      split; [apply x_actual_stream_reset|].
      split; [reflexivity|].
      split; [apply x_actual_reset|constructor].
    + exists hash, (x_actual_stream (1+a) b), hashR, hashLR,
        (x_actual_cut (1+a) b).
      split; [cbn; lia|].
      split; [apply x_actual_stream_shift|].
      split; [reflexivity|].
      split; [apply x_actual_shift|constructor].
  - constructor.
Qed.

Lemma x_initial_cycle_realizes:
  leftRealizes tm hashR (dollar_packets 40)
    x_initial_post_dollar.
Proof.
  rewrite x_initial_post_dollar_eq.
  rewrite <- x_actual_stream_initial.
  apply x_actual_cut_realizes_general.
Qed.

Lemma x_initial_cut_lcons:
  lcons hashR
    ((hashLR^^18) ++ hashLdollarR ++ dollarLhR) =
    (((hash^^19) ++ dollar),hashR).
Proof. vm_compute; reflexivity. Qed.

Lemma x_initial_cut_realizes:
  leftRealizes tm hashR
    (((hash^^19) ++ dollar) *> dollar_packets 40)
    x_initial_cut_left.
Proof.
  eapply sideRLs_leftRealizes_trans.
  - exact x_initial_cut_lcons.
  - exact x_initial_cut_signals.
  - exact x_initial_cycle_realizes.
Qed.

Definition x_event2325992_config :=
  x_initial_cut_left {{{ (hashR,R) }}}
    (x_initial_suffix_word *> x_preedge_side).

Lemma x_init_event2325992:
  c0 -[tm]->* x_event2325992_config.
Proof.
  eapply without_counter with (n:=2*(10^6)+325992).
  eapply multistep_c'_spec.
  native_check_eq.
Qed.

Theorem nonhalt:
  ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact x_init_event2325992.
  - unfold x_event2325992_config.
    eapply quadRect_nonhalt.
    + exact x_initial_suffix_quadRect.
    + exact x_initial_cut_realizes.
Qed.
