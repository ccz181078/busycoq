From BusyCoq Require Import Individual62.
From Coq Require Import Arith List String ZifyNat Lia.
Import ListNotations.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0RA_---0LD_1RE0LF_1RA0LB_1LD0LF").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Open Scope nat_scope.

Inductive digit := single (b:nat) | pair (a b:nat).
(* [pair a b] represents the source's (a,b+1), so its second entry is positive. *)
Inductive carry := hash | atsign | stop.

Definition local_step c d : option (digit * carry) :=
  match c,d with
  | hash,pair (S a) b => Some (pair a (S b),hash)
  | hash,pair 0 b => Some (single (b+2),stop)
  | hash,single (S b) => Some (pair b 0,atsign)
  | atsign,pair (S a) b => Some (pair a b,stop)
  | atsign,pair 0 b => Some (pair b 0,atsign)
  | atsign,single (S b) => Some (single b,stop)
  | stop,d => Some (d,stop)
  | _,single 0 => None
  end.

Fixpoint advance c ls : option (list digit) :=
  match ls with
  | [] => Some [single 1]
  | [single 0] => Some [single 1]
  | d::tail =>
      match local_step c d with
      | None => None
      | Some (d',stop) => Some (d'::tail)
      | Some (d',c') =>
          match advance c' tail with
          | Some tail' => Some (d'::tail')
          | None => None
          end
      end
  end.

Definition source_initial := [pair 1 0].

Definition stream_safe L R k g d : Prop :=
  R <= L /\
  match d with
  | pair a b => g=b /\
      ((a+b=k /\ a<=R /\ (k+1<=L \/ R+b<=L)) \/
       (a+b=k+1 /\ k+1<=L /\ R+b<=L))
  | single s =>
      (s=g+2 /\ k<=g /\ g+1<=L) \/
      (s=g+1 /\ k<=g /\ g+1<=L /\ g+1<=R)
  end.

Definition output_safe L R k g d c : Prop :=
  match c with
  | stop => stream_safe L R k g d
  | hash => stream_safe L R k (S g) d
  | atsign => k<=g /\ stream_safe L R g 0 d
  end.

Lemma stream_safe_nonzero L R k g :
  ~stream_safe L R k g (single 0).
Proof. unfold stream_safe; lia. Qed.

Theorem hash_stream_preserves L R k g d :
  stream_safe L (S R) k g d ->
  exists d' c, local_step hash d=Some (d',c) /\
    output_safe L R k g d' c.
Proof.
  destruct d as [s|a b]; unfold stream_safe; cbn; intros H.
  - destruct s as [|s]; [lia|].
    exists (pair s 0),atsign. split; [reflexivity|].
    unfold output_safe,stream_safe. cbn. lia.
  - destruct a as [|a].
    + exists (single (b+2)),stop. split; [reflexivity|].
      unfold output_safe,stream_safe. cbn. lia.
    + exists (pair a (S b)),hash. split; [reflexivity|].
      unfold output_safe,stream_safe. cbn. lia.
Qed.

Theorem atsign_stream_preserves L L' k g d :
  L<=L' -> stream_safe L 0 k g d ->
  exists d' c, local_step atsign d=Some (d',c) /\
    output_safe L' L' k g d' c.
Proof.
  destruct d as [s|a b]; unfold stream_safe; cbn; intros HL H.
  - destruct s as [|s]; [lia|].
    exists (single s),stop. split; [reflexivity|].
    unfold output_safe,stream_safe. cbn. lia.
  - destruct a as [|a].
    + exists (pair b 0),atsign. split; [reflexivity|].
      unfold output_safe,stream_safe. cbn. lia.
    + exists (pair a b),stop. split; [reflexivity|].
      unfold output_safe,stream_safe. cbn. lia.
Qed.

Lemma first_output_initializes L R :
  R<=L -> stream_safe L R 0 0 (pair 0 0).
Proof. unfold stream_safe. cbn. lia. Qed.


Lemma stream_safe_extend L R k g d :
  stream_safe L R k g d -> stream_safe (S L) (S R) k g d.
Proof. destruct d; unfold stream_safe; cbn; lia. Qed.

Definition input_safe p q := stream_safe (Nat.max p q) (p-q).
Definition output_history_safe p q := output_safe (Nat.max p q) (p-q).

Theorem hash_history_preserves p q k g d :
  input_safe p q k g d ->
  exists d' c, local_step hash d=Some(d',c) /\
    output_history_safe p (S q) k g d' c.
Proof.
  unfold input_safe,output_history_safe. intro H.
  destruct (Nat.lt_ge_cases q p) as [E|E].
  - replace (Nat.max p q) with p in H by lia.
    replace (Nat.max p (S q)) with p by lia.
    replace (p-q) with (S (p-S q)) in H by lia.
    exact (hash_stream_preserves _ _ _ _ _ H).
  - replace (Nat.max p q) with q in H by lia.
    replace (p-q) with 0 in H by lia.
    replace (Nat.max p (S q)) with (S q) by lia.
    replace (p-S q) with 0 by lia.
    exact (hash_stream_preserves _ _ _ _ _ (stream_safe_extend _ _ _ _ _ H)).
Qed.

Theorem atsign_history_preserves p q k g d :
  p<=q -> input_safe p q k g d ->
  exists d' c, local_step atsign d=Some(d',c) /\
    output_history_safe q 0 k g d' c.
Proof.
  unfold input_safe,output_history_safe. intros E H.
  replace (Nat.max p q) with q in H by lia.
  replace (p-q) with 0 in H by lia.
  replace (Nat.max q 0) with q by lia.
  replace (q-0) with q by lia.
  apply atsign_stream_preserves with (L:=q); [lia|exact H].
Qed.

(* Each active digit remembers its previous and current output gaps.
   A newly created last digit has emitted no output and can still be 0 or 1. *)
Inductive good : nat -> nat -> list digit -> Prop :=
| good_nil p q : good p q []
| good_zero p q : good p q [single 0]
| good_one p q : good p q [single 1]
| good_cons p q k g d ds :
    input_safe p q k g d -> good k g ds -> good p q (d::ds).

Lemma advance_cons_nonzero c d ds : d<>single 0 ->
  advance c (d::ds) =
  match local_step c d with
  | None => None
  | Some(d',stop) => Some(d'::ds)
  | Some(d',c') =>
      match advance c' ds with
      | None=>None | Some out=>Some(d'::out)
      end
  end.
Proof. destruct d as [[|s]|a b]; intros H; [contradiction|reflexivity|reflexivity]. Qed.

Lemma assemble_step p q k g d ds c d' c' :
  d<>single 0 -> good k g ds ->
  (exists out,advance hash ds=Some out /\ good k (S g) out) ->
  (k<=g -> exists out,advance atsign ds=Some out /\ good g 0 out) ->
  local_step c d=Some(d',c') -> output_history_safe p q k g d' c' ->
  exists out,advance c (d::ds)=Some out /\ good p q out.
Proof.
  intros Hz Hg HH HA E Hs.
  rewrite advance_cons_nonzero by exact Hz. rewrite E.
  destruct c'; unfold output_history_safe,output_safe in Hs.
  - destruct HH as [out [Ho Hgo]]. rewrite Ho.
    exists (d'::out). split; [reflexivity|]. eapply good_cons; eauto.
  - destruct Hs as [Hkg Hs]. destruct (HA Hkg) as [out [Ho Hgo]]. rewrite Ho.
    exists (d'::out). split; [reflexivity|]. eapply good_cons; eauto.
  - exists (d'::ds). split; [reflexivity|]. eapply good_cons; eauto.
Qed.

Theorem good_preserved p q ds : good p q ds ->
  (exists out, advance hash ds=Some out /\ good p (S q) out) /\
  (p<=q -> exists out, advance atsign ds=Some out /\ good q 0 out).
Proof.
  intro H; induction H as [p q|p q|p q|p q k g d ds Hs Hg IH].
  - split; [|intro]; exists [single 1]; split; [reflexivity|constructor|reflexivity|constructor].
  - split; [|intro]; exists [single 1]; split; [reflexivity|constructor|reflexivity|constructor].
  - split.
    + exists [pair 0 0; single 1]. split; [reflexivity|].
      apply good_cons with (k:=0) (g:=0); [|constructor].
      unfold input_safe. apply first_output_initializes. lia.
    + intro. exists [single 0]. split; [reflexivity|constructor].
  - assert (Hz:d<>single 0).
    { intro E; subst d. unfold input_safe in Hs. exact (stream_safe_nonzero _ _ _ _ Hs). }
    destruct IH as [HH HA]. split.
    + destruct (hash_history_preserves _ _ _ _ _ Hs) as [d' [c' [E Hout]]].
      eapply assemble_step; eauto.
    + intro Hpq.
      destruct (atsign_history_preserves _ _ _ _ _ Hpq Hs) as [d' [c' [E Hout]]].
      eapply assemble_step; eauto.
Qed.

Lemma initial_good : good 0 1 source_initial.
Proof.
  unfold source_initial. apply good_cons with (k:=0) (g:=0); [|constructor].
  unfold input_safe,stream_safe. cbn. lia.
Qed.


Open Scope sym_scope.
Fixpoint toRC ds := match ds with
| []=>0inf
| single b::ds=>[1;0]^^b *> 0 >> toRC ds
| pair a b::ds=>[1;0]^^a *> [0;0] *> [1;0]^^(1+b) *> 0 >> toRC ds end.

(* true = #; false = @. The padding makes both return in F. *)
Definition hR (c:bool) : DH0 := if c then (B,<[1;1]) else (E,<[1;1;0]).
Definition hL (c:bool) : DH0 := if c then (F,[0;0]) else (F,[0;0;1;0;0]).
Inductive RInc : bool -> list digit -> list digit -> Prop :=
| RInc_nil c : RInc c [] [single 1]
| RInc_zero c : RInc c [single 0] [single 1]
| RInc_hash_single b ds out : RInc false ds out ->
    RInc true (single (1+b)::ds) (pair b 0::out)
| RInc_hash_pair a b ds out : RInc true ds out ->
    RInc true (pair (1+a) b::ds) (pair a (1+b)::out)
| RInc_hash_zero b ds : RInc true (pair 0 b::ds) (single (2+b)::ds)
| RInc_at_single b ds : RInc false (single (1+b)::ds) (single b::ds)
| RInc_at_pair a b ds : RInc false (pair (1+a) b::ds) (pair a b::ds)
| RInc_at_zero b ds out : RInc false ds out ->
    RInc false (pair 0 b::ds) (pair b 0::out).

Lemma RInc_spec c ds out : RInc c ds out ->
  forall l, l {{{ (hR c,R) }}} toRC ds -->* l {{{ (hL c,L) }}} toRC out.
Proof.
  intro H; induction H; intros; try destruct c;
    cbn[hR hL toRC to_DH_config Str_app] in *;
    repeat (es; er; follow); es; er.
Qed.
Definition State n ds := 0inf <* <[1;1;0;1] << 0 <* <[1;0]^^(2+n) << 1 << 1 {{B}}> toRC ds.
Lemma sweep n ds out : RInc true ds out -> State n ds -->+ State (1+n) out.
Proof.
  intro H; eapply RInc_spec in H; unfold State;
    cbn[hR hL to_DH_config Str_app] in H; repeat (es; er; follow); es; er.
Qed.
Lemma init : c0 -->* State 1 [pair 1 0].
Proof. unfold State; cbn[toRC]; esx. Qed.

Open Scope nat_scope.
Lemma advance_RInc ds : forall (c:bool) out,
  advance (if c then hash else atsign) ds=Some out -> RInc c ds out.
Proof.
  induction ds as [|d ds IH]; intros c out H.
  - inversion H; subst; constructor.
  - destruct d as [[|b]|[|a] b].
    + destruct ds; [inversion H; subst; constructor|destruct c; discriminate].
    + destruct c; cbn[advance local_step] in H.
      * destruct (advance atsign ds) as [next|] eqn:E; [|discriminate].
        inversion H; subst; constructor; apply (IH false); exact E.
      * inversion H; subst; constructor.
    + destruct c; cbn[advance local_step] in H.
      * inversion H; subst; applys_eq RInc_hash_zero; flia.
      * destruct (advance atsign ds) as [next|] eqn:E; [|discriminate].
        inversion H; subst; constructor; apply (IH false); exact E.
    + destruct c; cbn[advance local_step] in H.
      * destruct (advance hash ds) as [next|] eqn:E; [|discriminate].
        inversion H; subst; constructor; apply (IH true); exact E.
      * inversion H; subst; constructor.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init|].
  eapply (progress_nonhalt_cond tm (nat*list digit) (1,source_initial)
    (fun '(n,ds)=>State n ds) (fun '(n,ds)=>good 0 n ds)).
  - intros [n ds] H.
    destruct (proj1 (good_preserved _ _ _ H)) as [out [E HG]].
    exists (1+n,out); split; [apply sweep, (advance_RInc ds true); exact E|exact HG].
  - exact initial_good.
Qed.

End TM1.
Print Assumptions TM1.nonhalt.
