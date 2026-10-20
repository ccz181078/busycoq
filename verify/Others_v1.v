(* OTHERS_29_20261020.txt, literal TM24 and TM25.
   Nonformal source invariant: OTHERS29_TM24_CAPS.txt.
   Both native blank-tape nonhalting theorems share the source proof. *)
From BusyCoq Require Import Individual62 Permute.
Require Import ZifyNat Lia PeanoNat String List.

Open Scope sym_scope.

Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_---0RE").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation hR := (D,<[0]).
Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).
Definition root (r:side) := 0inf <* [1] |> r.

(* The return through a single pending frame is a shift rule, provided
   the return head carries its three leading zeros. *)
Notation hBack := (E,[0;0;0]).

Lemma back_digit n:
  segLL tm hBack hBack ([0]++[1]^^(2+n)) ([0]^^n++[1;1;0]).
Proof. intros l r; esx. Qed.

Lemma start_back n l r:
  l <* [1]^^(2+n) <* [0] |> [0;0;0] *> r -->+
  l {{{ (hBack,L) }}} [0]^^(1+n) *> [1;1;0] *> r.
Proof. esx. Qed.

(* Heights are stored in physical left-to-right order; the left side
   remains a parameter, so this cannot erase an older pending block. *)
Definition pending (hs:list nat) (l:side) :=
  fold_left (fun l h => l <* [1]^^(2+h) <* [0]) hs l.
Definition back_word (hs:list nat) :=
  flat_map (fun h => [0]^^h++[1;1;0]) hs.

Lemma pending_back hs l r:
  pending hs l {{{ (hBack,L) }}} r -->*
  l {{{ (hBack,L) }}} back_word hs *> r.
Proof.
  gen l r; induction hs as [|h hs IH]; intros l r.
  - finish.
  - cbn [pending fold_left back_word flat_map].
    follow IH.
    follow (back_digit h).
    repeat rewrite Str_app_assoc; finish.
Qed.

Definition digits (ds:list nat) :=
  flat_map (fun d => [0]^^(1+d)++[1;1]) ds.

Lemma scan_digits ds:
  Forall (fun d => d<=1) ds ->
  forall l r,
  l |> digits ds *> r -->* pending ds l |> r.
Proof.
  intro H; induction H as [|d ds Hd Hds IH]; intros l r.
  - finish.
  - cbn [digits flat_map pending fold_left].
    repeat rewrite Str_app_assoc.
    assert (Hscan: forall l r, l |> [0]^^(1+d) *> [1;1] *> r -->*
      l <* [1]^^(2+d) <* [0] |> r).
    { destruct d as [|[|d]]; try lia; intros; esx. }
    follow Hscan; apply IH.
Qed.

Lemma ordinary_return ds n:
  Forall (fun d => d<=1) ds -> n<=1 ->
  forall l r,
  l |> digits ds *> [0]^^(1+n) *> [1;1;0;0;0] *> r -->+
  l {{{ (hBack,L) }}} back_word ds *> [0]^^(1+n) *> [1;1;0] *> r.
Proof.
  intros Hds Hn l r.
  follow (scan_digits ds Hds).
  assert (Hscan: forall l r, l |> [0]^^(1+n) *> [1;1] *> r -->*
    l <* [1]^^(2+n) <* [0] |> r).
  { destruct n as [|[|n]]; try lia; intros; esx. }
  follow Hscan.
  follow10 (start_back n).
  apply pending_back.
Qed.

Lemma zero_back_word ds r:
  0 >> back_word ds *> r = digits ds *> 0 >> r.
Proof.
  unfold back_word, digits.
  induction ds as [|d ds IH]; cbn [flat_map].
  - reflexivity.
  - repeat rewrite Str_app_assoc; cbn [lpow app Nat.add Str_app].
    cbn [Str_app] in IH.
    rewrite IH; reflexivity.
Qed.

Lemma close6 l r:
  l <* [0]^^6 {{{ (hBack,L) }}} r -->*
  l <* <[0;1] |> [0;0;1;1;1;0] *> r.
Proof. esx. Qed.

Lemma close2 l r:
  l <* [1]^^4 <* [0;0] {{{ (hBack,L) }}} r -->*
  l <{{A}} [1]^^8 *> [0] *> r.
Proof. esx. Qed.

Lemma block_back hs n l r:
  pending hs l <* [1]^^(2+n) <* [0] <{{A}} [1]^^8 *> r -->*
  l {{{ (hBack,L) }}} back_word hs *> [0]^^(1+n) *> [1]^^7 *> r.
Proof.
  assert (H: forall l r,
    l <* [1]^^(2+n) <* [0] <{{A}} [1]^^8 *> r -->*
    l {{{ (hBack,L) }}} [0]^^(1+n) *> [1]^^7 *> r).
  { intros; esx. }
  follow H; apply pending_back.
Qed.

Lemma last7 (b:nat) ds n l r:
  (b=1 \/ b=2)%nat -> Forall (fun d => d<=1) ds -> n<=1 ->
  l |> [0]^^b *> [1]^^7 *> digits ds *>
    [0]^^(1+n) *> [1;1;0;0;0] *> r -->+
  l <* [1]^^(1+b) <* <[0;1] |>
    [0;0;1;1;1] *> digits ds *> [0]^^(2+n) *> [1;1;0] *> r.
Proof.
  intros Hb Hds Hn.
  assert (Hscan: forall l r, l |> [0]^^b *> [1]^^7 *> r -->*
    l <* [1]^^(1+b) <* [0]^^6 |> r).
  { destruct Hb; subst; intros; esx. }
  follow Hscan.
  follow10 (ordinary_return ds n Hds Hn).
  follow close6.
  cbn [Str_app].
  rewrite zero_back_word.
  finish.
Qed.

Lemma active_scan l r:
  l <* [1] |> [0;0;1;1;1] *> r -->*
  l <* [1]^^4 <* [0;0] |> r.
Proof. esx. Qed.

Lemma active_turn l r:
  l <* [1] |> [0;0;1;1;1;0;0;0] *> r -->+
  l <* [1]^^3 <* [0] |> [0;0;1;1;0] *> r.
Proof. esx. Qed.

Definition payload (ds:list nat) :=
  flat_map (fun d => [0]^^d++[1;1]) ds.

Definition put_left (hs:list nat) (l:side) :=
  fold_left (fun l h => l <* [1]^^h <* [0]) hs l.

Definition seed := [2;2;1;2;2;1;2]%nat.

(* The fixed parts of the four cap bridges.  The whole right suffix is
   arbitrary; the subsequent variable-length constructor is separate. *)
Definition cap_entry ds h (r:side) :=
  root ([0;0] *> payload ds *> [0]^^h *> [1]^^7 *> r).

Lemma bridge0 r:
  cap_entry [] 4 r -->+
  put_left [3] 0inf |> payload [2] *> [0;0] *> [1]^^7 *> r.
Proof. esx. Qed.

Lemma bridge1 r:
  cap_entry [2;2] 3 r -->+
  put_left [4;3] 0inf |> payload [2;1;1]%nat *> [0] *> [1]^^7 *> r.
Proof. esx. Qed.

Lemma bridge2 r:
  cap_entry [3;2;2;1;1]%nat 2 r -->+
  put_left [3] 0inf |> payload [2;1;2;2;1;1]%nat *> [0;0] *> [1]^^7 *> r.
Proof. esx. Qed.

Lemma bridge3 r:
  cap_entry [2;2;1;2;2;1;1]%nat 3 r -->+
  root ([0;0] *> [1]^^7 *> payload seed *> [0] *> [1]^^7 *> r).
Proof. esx. Qed.

(* A fixed-width value: the source length guards ensure that all seven
   positions exist.  Proving the cut lemma for arbitrary n avoids
   enumerating the possible positions of a carry. *)
Open Scope nat_scope.
Fixpoint prefix_value (n:nat) (ds:list nat) : nat :=
  match n,ds with
  | S k,d::ds => d*2^k + prefix_value k ds
  | _,_ => 0
  end.

Lemma prefix_carry n u a t:
  prefix_value n (u++[a;3]++t) <=
  prefix_value n (u++[1+a;1]++t) <=
  1+prefix_value n (u++[a;3]++t).
Proof.
  gen n; induction u as [|d u IH]; intros [|n]; cbn [app prefix_value].
  - lia.
  - destruct n; cbn [prefix_value Nat.pow]; nia.
  - lia.
  - specialize (IH n); cbn [app] in IH; lia.
Qed.

Lemma prefix_last n u a:
  n<=1+length u ->
  prefix_value n (u++[a]) <= prefix_value n (u++[1+a]) <=
  1+prefix_value n (u++[a]).
Proof.
  gen n; induction u as [|d u IH]; intros [|n] H; cbn in *.
  - lia.
  - assert (n=0) by lia; subst; cbn; lia.
  - lia.
  - specialize (IH n); lia.
Qed.

(* Ordinary gaps are stored minus one, as in [digits].
   Tail permits one carry digit2, followed only by zeros.
   Num additionally tracks the parity of the initial run of ones:
   false for an active prefix, true for a seven-run's payload.
   A zero ends that initial-run condition; the full tail is retained. *)
Inductive Tail : list nat -> Prop :=
| TNil: Tail []
| TZero ds: Tail ds -> Tail (0::ds)
| TOne ds: Tail ds -> Tail (1::ds)
| TTwo n: Tail (2::repeat 0 n).

Inductive Num : bool -> list nat -> Prop :=
| NNil p: Num p []
| NZero p ds: Tail ds -> Num p (0::ds)
| NOne p ds: Num (negb p) ds -> Num p (1::ds)
| NTwo n: Num false (2::repeat 0 n).

Lemma tail_zeros n: Tail (repeat 0 n).
Proof. induction n; constructor; auto. Qed.

Lemma tail_prefix u t:
  Forall (fun d => d<=1) u -> Tail t -> Tail (u++t).
Proof.
  intros H; induction H as [|d u Hd Hu IH]; cbn [app]; auto.
  destruct d as [|[|d]]; try lia; intro Ht; constructor; auto.
Qed.

Lemma tail_binary u: Forall (fun d => d<=1) u -> Tail u.
Proof.
  intro H; induction H as [|d u Hd Hu IH]; [constructor|].
  destruct d as [|[|d]]; try lia; constructor; assumption.
Qed.

Lemma num_binary u:
  Forall (fun d => d<=1) u -> forall p, Num p u.
Proof.
  intro H; induction H as [|d u Hd Hu IH]; intro p.
  - constructor.
  - destruct d as [|[|d]]; try lia; constructor; auto.
    apply tail_binary; assumption.
Qed.

Lemma num_tail p ds: Num p ds -> Tail ds.
Proof. intro H; induction H; constructor; auto. Qed.

Lemma num_one p ds: Num p (1::ds) -> Num (negb p) ds.
Proof. intro H; inverts H; assumption. Qed.

Lemma num_two p ds: Num p (2::ds) -> p=false.
Proof. intro H; inverts H; reflexivity. Qed.

Lemma tail_bump u a n:
  Forall (fun d => d<=1) u -> a<=1 ->
  Tail (u++[1+a]++repeat 0 n).
Proof.
  intros Hu Ha; apply tail_prefix; [apply Hu|].
  destruct a as [|[|a]]; try lia; cbn; constructor; apply tail_zeros.
Qed.

Lemma num_carry p u a n:
  Forall (fun d => d<=1) u -> a<=1 ->
  Num p (u++[a;2]++repeat 0 n) ->
  Num (negb p) (u++[1+a;0]++repeat 0 n).
Proof.
  intros Hu Ha; gen p; induction Hu as [|d u Hd Hu IH]; intros p H.
  - destruct a as [|[|a]]; try lia; cbn [app Nat.add] in *.
    + constructor; constructor; apply tail_zeros.
    + apply num_one, num_two in H.
      destruct p; [apply (NTwo (1+n))|discriminate].
  - destruct d as [|[|d]]; try lia; cbn [app] in *.
    + constructor; apply (tail_bump u a (1+n) Hu Ha).
    + constructor; apply num_one in H.
      specialize (IH (negb p) H); now rewrite Bool.negb_involutive in *.
Qed.

Fixpoint mass (ds:list nat) : nat :=
  match ds with []=>0 | d::ds=>1+d+mass ds end.

Lemma mass_app u v: mass (u++v)=mass u+mass v.
Proof. induction u; cbn [mass app]; lia. Qed.

Lemma mass_zeros n: mass (repeat 0 n)=n.
Proof. induction n; cbn [mass repeat]; lia. Qed.

Lemma mass_ones u:
  Forall (eq 1) u -> Nat.odd (mass u)=false.
Proof.
  intro H; induction H; subst; cbn [mass]; auto.
Qed.

Lemma odd_next n: Nat.odd (1+n)=negb (Nat.odd n).
Proof. rewrite Nat.odd_succ, Nat.negb_odd; reflexivity. Qed.

(* The length tag distinguishes terminal/internal records.  The mass
   includes the implicit +1 of each stored gap, not just its offset. *)
Definition Tags p b ds :=
  Nat.odd (length ds)=negb (b=?0) /\ Nat.odd (mass ds+b)=p.
Definition Head p ds :=
  match ds with []=>False | d::_=>d=1 \/ (d=2 /\ p=false) end.
Definition Segment p b ds :=
  Num p ds /\ Head p ds /\ Tags p b ds /\
  7+(if b=?0 then 1 else 0)<=length ds.

Lemma num_end p u:
  Forall (fun d=>d<=1) u ->
  (Forall (eq 1) u -> p=Nat.odd (length u)) ->
  Num p (u++[2]).
Proof.
  intro Hu; gen p; induction Hu as [|d u Hd Hu IH]; intros p H.
  - specialize (H (Forall_nil _)); subst; apply (NTwo 0).
  - destruct d as [|[|d]]; try lia; cbn [app].
    + constructor; apply tail_prefix; [apply Hu|apply (TTwo 0)].
    + constructor; apply IH; intro Hone.
      specialize (H ltac:(constructor; auto)).
      cbn [length] in H.
      now rewrite H, Nat.odd_succ, Nat.negb_even.
Qed.

Lemma num_last_tags p b u a:
  Forall (fun d=>d<=1) u -> a<=1 ->
  Tags p b (u++[a]) -> (b=0 \/ b=3) ->
  Num (negb p) (u++[1+a]).
Proof.
  intros Hu Ha [Hlen Hsum] Hb.
  destruct a as [|[|a]]; try lia.
  - apply num_binary, Forall_app; split; auto.
  - apply num_end; [apply Hu|]; intro Hone.
    rewrite mass_app in Hsum; cbn [mass] in Hsum.
    rewrite !Nat.odd_add, (mass_ones u Hone) in Hsum; cbn in Hsum.
    rewrite length_app in Hlen; cbn [length] in Hlen.
    rewrite Nat.add_1_r, Nat.odd_succ in Hlen.
    destruct Hb; subst b; cbn in Hsum,Hlen; subst p;
      now rewrite <-Nat.negb_even, Hlen.
Qed.

Lemma tags_carry p b u a n:
  Tags p b (u++[a;2]++repeat 0 n) ->
  Tags (negb p) b (u++[1+a;0]++repeat 0 n).
Proof.
  intros [Hlen Hsum]; split.
  - repeat rewrite length_app in *; cbn [length] in *; exact Hlen.
  - assert (E: mass (u++[a;2]++repeat 0 n)+b =
               1+(mass (u++[1+a;0]++repeat 0 n)+b)).
    { repeat rewrite mass_app; cbn [mass]; lia. }
    rewrite E, odd_next in Hsum.
    now rewrite <-Hsum, Bool.negb_involutive.
Qed.

Lemma head_carry p u a n:
  Forall (fun d=>d<=1) u -> a<=1 ->
  Num p (u++[a;2]++repeat 0 n) ->
  Head p (u++[a;2]++repeat 0 n) ->
  Head (negb p) (u++[1+a;0]++repeat 0 n).
Proof.
  intros Hu Ha Hnum Hhead; destruct u as [|d u].
  - cbn [app Head] in *.
    assert (a=1) by (destruct Hhead as [H|[H _]]; lia).
    subst; right; split; [reflexivity|].
    apply num_one, num_two in Hnum; exact Hnum.
  - assert (Hd:d<=1) by (inversion Hu; assumption).
    cbn [app Head] in *; left.
    destruct Hhead as [H|[H _]]; lia.
Qed.

Lemma segment_carry p b u a n:
  Forall (fun d=>d<=1) u -> a<=1 ->
  Segment p b (u++[a;2]++repeat 0 n) ->
  Segment (negb p) b (u++[1+a;0]++repeat 0 n).
Proof.
  intros Hu Ha [HN [HH [HT HL]]].
  split; [eapply num_carry; eauto|].
  split; [eapply head_carry; eauto|].
  split; [apply tags_carry; assumption|].
  repeat rewrite length_app in *; cbn [length] in *; exact HL.
Qed.

Lemma odd_adjacent x y:
  x=1+y \/ y=1+x -> Nat.odd y=negb (Nat.odd x).
Proof.
  intros [H|H]; subst; rewrite odd_next;
    try rewrite Bool.negb_involutive; reflexivity.
Qed.

Lemma tags_last p b u a:
  Tags p b (u++[a]) -> (b=0 \/ b=3) ->
  Tags (negb p) (b-2) (u++[1+a]).
Proof.
  intros [Hlen Hsum] Hb; split.
  - destruct Hb; subst b; cbn [Nat.sub Nat.eqb] in *;
      repeat rewrite length_app in *; cbn [length] in *; exact Hlen.
  - rewrite <-Hsum; apply odd_adjacent.
    destruct Hb; subst b; cbn [Nat.sub];
      repeat rewrite mass_app; cbn [mass]; lia.
Qed.

Lemma segment_last p b u a:
  Forall (fun d=>d<=1) u -> a<=1 ->
  Segment p b (u++[a]) -> (b=0 \/ b=3) ->
  Segment (negb p) (b-2) (u++[1+a]).
Proof.
  intros Hu Ha [HN [HH [HT HL]]] Hb.
  split; [eapply num_last_tags; eauto|].
  split.
  - destruct u as [|d u].
    + cbn [app length] in HL; lia.
    + assert (Hd:d<=1) by (inversion Hu; assumption).
      cbn [app Head] in *; left.
      destruct HH as [H|[H _]]; lia.
  - split; [apply tags_last; assumption|].
    destruct Hb; subst b; cbn [Nat.sub Nat.eqb] in *;
      repeat rewrite length_app in *; cbn [length] in *; exact HL.
Qed.

Lemma head_binary p ds:
  Forall (fun d=>d<=1) ds -> Head p ds -> Head true ds.
Proof.
  intros H HH; destruct ds as [|d ds]; [exact HH|].
  inversion H; cbn [Head] in *; left.
  destruct HH as [HH|[HH _]]; lia.
Qed.

Lemma head_any p ds: Head true ds -> Head p ds.
Proof.
  destruct ds; cbn [Head]; [tauto|].
  intros [H|[_ H]]; [left; assumption|discriminate].
Qed.

(* A scanned block stores binary offsets, with its final height separate.
   The parity tag is inherited from the payload that created it.
   On return, its header increases by one and its payload phase flips. *)
Definition Block p '(ds,n) :=
  Forall (fun d=>d<=1) ds /\ n<=1 /\ Head true ds /\
  Tags p (1+n) ds /\ 7<=length ds.

Lemma block_length p ds n: Block p (ds,n) -> 7<=length ds.
Proof. intros [_ [_ [_ [_ H]]]]; exact H. Qed.

Lemma scanned_block p b ds:
  Segment p b ds -> Forall (fun d=>d<=1) ds ->
  (b=1 \/ b=2) -> Block p (ds,b-1).
Proof.
  intros [HN [HH [[Hlen Hsum] HL]]] Hu Hb.
  destruct Hb; subst b; unfold Block; cbn [Nat.sub Nat.add];
    repeat split; auto; try lia; eapply head_binary; eauto.
Qed.

Lemma emitted_segment p ds n:
  Block p (ds,n) -> Segment (negb p) (2+n) ds.
Proof.
  intros [Hu [Hn [HH [[Hlen Hsum] HL]]]].
  split; [apply num_binary; assumption|].
  split; [apply head_any; assumption|].
  split.
  - split.
    + cbn [Nat.add Nat.eqb] in *; exact Hlen.
    + rewrite <-Hsum; apply odd_adjacent; right; lia.
  - cbn [Nat.add Nat.eqb]; lia.
Qed.

Lemma tail_split ds:
  Tail ds ->
  Forall (fun d=>d<=1) ds \/
  exists u n, Forall (fun d=>d<=1) u /\ ds=u++2::repeat 0 n.
Proof.
  intro H; induction H as [|ds H IH|ds H IH|n].
  - left; constructor.
  - destruct IH as [Hb|[u [n [Hu E]]]].
    + left; constructor; auto.
    + right; exists (0::u),n; split; [constructor; auto|now subst].
  - destruct IH as [Hb|[u [n [Hu E]]]].
    + left; constructor; auto.
    + right; exists (1::u),n; split; [constructor; auto|now subst].
  - right; exists ([]:list nat),n; split; [constructor|reflexivity].
Qed.

Inductive Carry : list nat -> nat -> list nat -> nat -> Prop :=
| CInside u a n b:
  Forall (fun d=>d<=1) u -> a<=1 ->
  Carry (u++[a;2]++repeat 0 n) b (u++[1+a;0]++repeat 0 n) b
| CLast u a b:
  Forall (fun d=>d<=1) u -> a<=1 -> (b=0 \/ b=3) ->
  Carry (u++[a]) b (u++[1+a]) (b-2).

Lemma carry_segment p ds b ds' b':
  Carry ds b ds' b' -> Segment p b ds -> Segment (negb p) b' ds'.
Proof.
  intro H; destruct H; eauto using segment_carry, segment_last.
Qed.

Lemma carry_zero ds ds' b':
  Carry ds 0 ds' b' -> b'=0.
Proof. intro H; inverts H; reflexivity. Qed.

Lemma carry_header ds b ds' b':
  Carry ds b ds' b' -> 1<=b<=3 -> 1<=b'<=3.
Proof. intro H; destruct H; lia. Qed.

Lemma word_progress b ds:
  Tail ds -> Head true ds -> b<=3 ->
  (exists ds' b', Carry ds b ds' b') \/
  (Forall (fun d=>d<=1) ds /\ (b=1 \/ b=2)).
Proof.
  intros HN HH Hb.
  destruct (tail_split ds HN) as [Hd|[u [n [Hu E]]]].
  - assert (Hb': (b=0 \/ b=3) \/ (b=1 \/ b=2)) by lia.
    destruct Hb' as [Hb'|Hb']; [left|right; auto].
    assert (Hne:ds<>[]) by (intro E; subst; exact HH).
    destruct (exists_last Hne) as [u [a E]]; subst ds.
    apply Forall_app in Hd; destruct Hd as [Hu Ha]; inversion Ha.
    eexists; eexists; apply CLast; eauto.
  - left.
    assert (Hne:u<>[]).
    { intro Eu; subst; cbn [app Head] in HH.
      destruct HH as [H|[_ H]]; discriminate. }
    destruct (exists_last Hne) as [v [a Eu]]; subst u.
    apply Forall_app in Hu; destruct Hu as [Hv Ha]; inversion Ha.
    rewrite <-app_assoc in E; cbn [app] in E; subst ds.
    eexists; eexists; apply CInside; eauto.
Qed.

Lemma record_progress b ds:
  Segment true b ds -> b<=3 ->
  (exists ds' b', Carry ds b ds' b') \/
  (Forall (fun d=>d<=1) ds /\ (b=1 \/ b=2)).
Proof.
  intros [HN [HH _]] Hb; apply word_progress; auto.
  eapply num_tail; eauto.
Qed.

Lemma segment_progress b ds:
  Segment false b ds -> b<=3 ->
  (exists k, ds=2::repeat 0 k) \/
  (exists ds' b', Carry ds b ds' b') \/
  (Forall (fun d=>d<=1) ds /\ (b=1 \/ b=2)).
Proof.
  intros [HN [HH _]] Hb; destruct ds as [|d ds]; [contradiction|].
  destruct HH as [H|[H _]]; subst d.
  - right; apply word_progress; [eapply num_tail; eauto|left; reflexivity|exact Hb].
  - left; inverts HN; eauto.
Qed.

(* Records retain every payload and every following seven-run header.
   No global synchronization or bounded record count is assumed. *)
Inductive Records :=
| REnd (ds:list nat)
| RMore (ds:list nat) (b:nat) (rs:Records).

Fixpoint Good p rs : Prop :=
  match rs with
  | REnd ds => Segment p 0 ds
  | RMore ds b rs => Segment p b ds /\ 1<=b<=3 /\ Good true rs
  end.

Inductive Advance : Records -> list (list nat*nat) -> Records -> Prop :=
| AEnd ds ds':
  Carry ds 0 ds' 0 -> Advance (REnd ds) [] (REnd ds')
| AStop ds b ds' b' rs:
  0<b -> Carry ds b ds' b' ->
  Advance (RMore ds b rs) [] (RMore ds' b' rs)
| AGo ds b rs bs rs':
  Forall (fun d=>d<=1) ds -> (b=1 \/ b=2) ->
  Advance rs bs rs' ->
  Advance (RMore ds b rs) ((ds,b-1)::bs) rs'.

Lemma advance_total rs:
  Good true rs ->
  exists bs rs', Advance rs bs rs' /\
    Forall (Block true) bs /\ Good false rs'.
Proof.
  induction rs as [ds|ds b rs IH]; cbn [Good]; intro H.
  - destruct (record_progress 0 ds H ltac:(lia)) as [[ds' [b' HC]]|[_ Hb]].
    + apply carry_zero in HC as E; subst b'.
      exists ([]:list (list nat*nat)),(REnd ds'); split.
      * constructor; assumption.
      * split.
        -- apply Forall_nil.
        -- cbn [Good]; eapply (carry_segment true); eauto.
    + lia.
  - destruct H as [HS [Hb HR]].
    destruct (record_progress b ds HS ltac:(lia)) as [[ds' [b' HC]]|[HD HB]].
    + exists ([]:list (list nat*nat)),(RMore ds' b' rs); split.
      * constructor; [lia|assumption].
      * split; [apply Forall_nil|].
        cbn [Good]; split; [eapply (carry_segment true); eauto|].
        split; [eapply carry_header; eauto|assumption].
    + destruct (IH HR) as [bs [rs' [HA [HBs HG]]]].
      exists ((ds,b-1)::bs),rs'; split; [constructor; assumption|].
      split; [constructor; [eapply scanned_block; eauto|assumption]|assumption].
Qed.

Definition measure ds := prefix_value 7 (map S ds).
Definition first_digits rs :=
  match rs with REnd ds | RMore ds _ _ => ds end.
Definition protected (bs:list (list nat*nat)) rs :=
  match bs with []=>first_digits rs | (ds,_)::_=>ds end.

Lemma segment_length p b ds: Segment p b ds -> 7<=length ds.
Proof. intros [_ [_ [_ H]]]; lia. Qed.

Lemma carry_bound ds b ds' b':
  Carry ds b ds' b' -> 7<=length ds ->
  measure ds'<=1+measure ds.
Proof.
  intros H HL; destruct H; unfold measure;
    rewrite !map_app; cbn [map].
  - exact (proj2 (prefix_carry 7 (map S u) (S a) (map S (repeat 0 n)))).
  - apply (proj2 (prefix_last 7 (map S u) (S a) ltac:(
      rewrite length_map; rewrite length_app in HL; cbn [length] in HL; lia))).
Qed.

Lemma advance_bound rs bs rs':
  Advance rs bs rs' -> Good true rs ->
  measure (protected bs rs')<=1+measure (first_digits rs).
Proof.
  intro H; destruct H; cbn [Good protected first_digits]; intro HG.
  - eapply carry_bound; [eassumption|eapply segment_length; eauto].
  - destruct HG as [HS _].
    eapply carry_bound; [eassumption|eapply segment_length; eauto].
  - lia.
Qed.

Lemma carry_not_scan ds b ds' b':
  Carry ds b ds' b' -> Forall (fun d=>d<=1) ds ->
  (b=1 \/ b=2) -> False.
Proof.
  intro H; destruct H; intros HD Hb; [|lia].
  rewrite Forall_forall in HD.
  assert (Hbad:2<=1) by (apply HD; apply in_or_app; right; cbn; auto).
  lia.
Qed.

Lemma advance_go ds b rs bs rs':
  Advance (RMore ds b rs) bs rs' ->
  Forall (fun d=>d<=1) ds -> (b=1 \/ b=2) ->
  exists bs', bs=(ds,b-1)::bs' /\ Advance rs bs' rs'.
Proof.
  intros H HD Hb; inverts H.
  - exfalso; eapply carry_not_scan; eauto.
  - eexists; split; [reflexivity|eassumption].
Qed.

Definition seed_offset := [1;1;0;1;1;0;1].

Lemma seed_binary: Forall (fun d=>d<=1) seed_offset.
Proof. repeat constructor; lia. Qed.

Lemma seed_segment: Segment true 1 seed_offset.
Proof.
  split; [apply num_binary, seed_binary|].
  unfold seed_offset, Head, Tags; cbn [length mass]; repeat split; auto; lia.
Qed.

Lemma seed_measure: measure seed_offset=236.
Proof. reflexivity. Qed.

Open Scope sym_scope.

Lemma digits_app u v: digits (u++v)=digits u++digits v.
Proof. unfold digits; apply flat_map_app. Qed.

Lemma scan_seven b l r:
  (b=1 \/ b=2)%nat ->
  l |> [0]^^b *> [1]^^7 *> r -->*
  l <* [1]^^(1+b) <* [0]^^6 |> r.
Proof. intros [H|H]; subst; esx. Qed.

Lemma last7_snoc b u a l r:
  (b=1 \/ b=2)%nat -> Forall (fun d=>d<=1) u -> a<=1 ->
  l |> [0]^^b *> [1]^^7 *> digits (u++[a]) *> [0;0;0] *> r -->+
  l <* [1]^^(1+b) <* [0] <* [1] |>
    [0;0;1;1;1] *> digits (u++[1+a]) *> [0] *> r.
Proof.
  intros Hb Hu Ha.
  rewrite !digits_app; cbn [digits flat_map]; repeat rewrite Str_app_assoc.
  follow10 (last7 b u a l r Hb Hu Ha); finish.
Qed.

Lemma last7_inside b u a n l r:
  (b=1 \/ b=2)%nat -> Forall (fun d=>d<=1) u -> a<=1 ->
  l |> [0]^^b *> [1]^^7 *> digits (u++[a;2]++repeat 0 n)%nat *> r -->+
  l <* [1]^^(1+b) <* [0] <* [1] |>
    [0;0;1;1;1] *> digits (u++[1+a;0]++repeat 0 n)%nat *> r.
Proof.
  intros Hb Hu Ha.
  rewrite !digits_app; cbn [digits flat_map]; repeat rewrite Str_app_assoc.
  follow10 (last7 b u a l ([1;1] *> digits (repeat 0%nat n) *> r) Hb Hu Ha).
  finish.
Qed.

Lemma last7_blank b u a l:
  (b=1 \/ b=2)%nat -> Forall (fun d=>d<=1) u -> a<=1 ->
  l |> [0]^^b *> [1]^^7 *> digits (u++[a]) *> 0inf -->+
  l <* [1]^^(1+b) <* [0] <* [1] |>
    [0;0;1;1;1] *> digits (u++[1+a]) *> 0inf.
Proof.
  intros Hb Hu Ha; generalize (last7_snoc b u a l 0inf Hb Hu Ha).
  cbn [Str_app]; repeat rewrite <-const_unfold; auto.
Qed.

Fixpoint records_side rs : side :=
  match rs with
  | REnd ds => digits ds *> 0inf
  | RMore ds b rs => digits ds *> [0]^^b *> [1]^^7 *> records_side rs
  end.

Definition record_stack bs (l:side) :=
  fold_left (fun l '(ds,n) =>
    pending ds (l <* [0]^^5) <* [1]^^(2+n) <* [0]) bs l.

Lemma advance_spec rs bs rs':
  Advance rs bs rs' -> forall h l,
  (h=1 \/ h=2)%nat ->
  l |> [0]^^h *> [1]^^7 *> records_side rs -->+
  record_stack bs (l <* [1]^^(1+h) <* [0]) <* [1] |>
    [0;0;1;1;1] *> records_side rs'.
Proof.
  intro H; induction H as
    [ds ds' HC|ds b ds' b' rs Hb HC|ds b rs bs rs' HD HB HA IH];
    intros h l Hh; cbn [records_side record_stack fold_left].
  - inverts HC; [apply last7_inside|apply last7_blank]; assumption.
  - inverts HC.
    + apply last7_inside; assumption.
    + assert (b=3)%nat by lia; subst b.
      apply last7_snoc; assumption.
  - follow (scan_seven h l
      (digits ds *> [0]^^b *> [1]^^7 *> records_side rs) Hh).
    follow (scan_digits ds HD).
    follow10 (IH b (pending ds (l <* [1]^^(1+h) <* [0]^^6)) HB).
    destruct HB; subst b; finish.
Qed.

(* The fourth cap bridge must cross the seed's following seven-run.
   It therefore creates a real six-zero separator and copies all seven
   seed digits into the first new pending block, even if later records
   are scanned too. *)
Lemma reset_rule rs:
  Good true rs ->
  exists bs rs',
  Forall (Block true) ((seed_offset,0%nat)::bs) /\ Good false rs' /\
  (cap_entry [2;2;1;2;2;1;1]%nat 3 (records_side rs) -->+
   record_stack ((seed_offset,0%nat)::bs) (put_left [4] 0inf) <* [1] |>
     [0;0;1;1;1] *> records_side rs').
Proof.
  intro HR.
  assert (HG:Good true (RMore seed_offset 1 rs)).
  { cbn [Good]; split; [apply seed_segment|]; split; [lia|assumption]. }
  destruct (advance_total _ HG) as [bs [rs' [HA [HB HG']]]].
  destruct (advance_go _ _ _ _ _ HA seed_binary ltac:(left; reflexivity))
    as [bs' [E Hnext]]; subst bs.
  exists bs',rs'; split; [exact HB|]; split; [exact HG'|].
  follow11 (bridge3 (records_side rs)).
  apply (advance_spec _ _ _ HA 2 (0inf <* [1]) ltac:(right; reflexivity)).
Qed.

Open Scope nat_scope.
Inductive Cap := C0 | C1 | C2 | C3.
Definition cap_word c : list nat :=
  match c with
  | C0=>[4] | C1=>[3;3;3] | C2=>[4;3;3;2;2;2]
  | C3=>[3;3;2;3;3;2;2;3]
  end.
Definition cap_prefix c : list nat :=
  match c with
  | C0=>[] | C1=>[2;2] | C2=>[3;2;2;1;1]
  | C3=>[2;2;1;2;2;1;1]
  end.
Definition cap_height c :=
  match c with C0=>4 | C1=>3 | C2=>2 | C3=>3 end.
Definition cap_bound c :=
  match c with C0=>236 | C1=>238 | C2=>240 | C3=>242 end.
Definition next_cap c :=
  match c with C0=>C1 | C1=>C2 | C2=>C3 | C3=>C0 end.

Open Scope sym_scope.
Lemma cap_prefix_spec c rs bs rs':
  c<>C3 -> Advance rs bs rs' ->
  cap_entry (cap_prefix c) (cap_height c) (records_side rs) -->+
  record_stack bs (put_left (cap_word (next_cap c)) 0inf) <* [1] |>
    [0;0;1;1;1] *> records_side rs'.
Proof.
  intros Hc HA; destruct c; [| | |contradiction].
  - follow11 (bridge0 (records_side rs)).
    follow (scan_digits [1]%nat ltac:(repeat constructor; lia)).
    apply (advance_spec _ _ _ HA 2
      (pending [1]%nat (put_left [3] 0inf)) ltac:(right; reflexivity)).
  - follow11 (bridge1 (records_side rs)).
    follow (scan_digits [1;0;0]%nat ltac:(repeat constructor; lia)).
    apply (advance_spec _ _ _ HA 1
      (pending [1;0;0]%nat (put_left [4;3] 0inf)) ltac:(left; reflexivity)).
  - follow11 (bridge2 (records_side rs)).
    follow (scan_digits [1;0;1;1;0;0]%nat ltac:(repeat constructor; lia)).
    apply (advance_spec _ _ _ HA 2
      (pending [1;0;1;1;0;0]%nat (put_left [3] 0inf)) ltac:(right; reflexivity)).
Qed.

Lemma cap_rule c rs:
  Good true rs -> measure (first_digits rs)<=1+cap_bound c ->
  exists bs rs', Forall (Block true) bs /\ Good false rs' /\
  measure (protected bs rs')<=cap_bound (next_cap c) /\
  (cap_entry (cap_prefix c) (cap_height c) (records_side rs) -->+
   record_stack bs (put_left (cap_word (next_cap c)) 0inf) <* [1] |>
     [0;0;1;1;1] *> records_side rs').
Proof.
  intros HG HM; destruct c.
  1-3: destruct (advance_total rs HG) as [bs [rs' [HA [HB HR]]]];
    exists bs,rs'; split; [exact HB|]; split; [exact HR|]; split;
    [generalize (advance_bound _ _ _ HA HG);
     cbn [cap_bound next_cap] in *; lia
    |apply cap_prefix_spec; [discriminate|exact HA]].
  destruct (reset_rule rs HG) as [bs [rs' [HB [HR HS]]]].
  exists ((seed_offset,0%nat)::bs),rs'; split; [exact HB|].
  split; [exact HR|]; split;
    [cbn [protected cap_bound next_cap]; rewrite seed_measure; reflexivity|exact HS].
Qed.

(* Two head zeros make the returned suffix a complete record chain.
   The third zero required by the local kernel must still be supplied
   by that suffix; it is not safe to drop this guard for arbitrary tails. *)
Notation hReturn := (E,[0;0]).

Lemma records_zero p rs:
  Good p rs -> exists r, records_side rs=0 >> r.
Proof.
  destruct rs as [ds|ds b rs]; cbn [Good records_side];
    intros H; destruct ds as [|d ds].
  - destruct H as [_ [H _]]; contradiction.
  - eexists; reflexivity.
  - destruct H as [[_ [H _]] _]; contradiction.
  - eexists; reflexivity.
Qed.

Lemma return_separator l r:
  (exists r', r=0 >> r') ->
  l <* [1]^^4 <* [0;0] {{{ (hReturn,L) }}} r -->*
  l <{{A}} [1]^^8 *> r.
Proof. intros [r' E]; subst r; apply close2. Qed.

Lemma return_six l r:
  (exists r', r=0 >> r') ->
  l <* [0]^^6 {{{ (hReturn,L) }}} r -->*
  l <* <[0;1] |> [0;0;1;1;1] *> r.
Proof. intros [r' E]; subst r; apply close6. Qed.

Lemma emit_block ds n l r:
  pending ds l <* [1]^^(2+n) <* [0] <{{A}} [1]^^8 *> r -->*
  l {{{ (hReturn,L) }}} digits ds *> [0]^^(2+n) *> [1]^^7 *> r.
Proof.
  follow (block_back ds n).
  change (l {{{ (hReturn,L) }}} 0 >> back_word ds *>
    [0]^^(1+n) *> [1]^^7 *> r -->*
    l {{{ (hReturn,L) }}} digits ds *> [0]^^(2+n) *> [1]^^7 *> r).
  rewrite zero_back_word; finish.
Qed.

Inductive Stack :=
| SCap (c:Cap)
| SPush (six:bool) (older:Stack) (ds:list nat) (n:nat).

Fixpoint stack_good st :=
  match st with
  | SCap _ => True
  | SPush six older ds n => stack_good older /\ Block six (ds,n)
  end.

Fixpoint stack_side st : side :=
  match st with
  | SCap c => put_left (cap_word c) 0inf
  | SPush six older ds n =>
    pending ds (if six then stack_side older <* [0]^^5
      else stack_side older <* [1]^^4 <* [0;0]) <*
    [1]^^(2+n) <* [0]
  end.

Fixpoint stack_cap st :=
  match st with SCap c=>c | SPush _ older _ _=>stack_cap older end.

Fixpoint stack_protected st ds :=
  match st with
  | SCap _=>ds
  | SPush _ older prefix _=>stack_protected older prefix
  end.

Lemma stack_zero st: exists l, stack_side st=0 >> l.
Proof. destruct st as [[]|]; eexists; reflexivity. Qed.

Definition active st rs :=
  stack_side st <* [1] |> [0;0;1;1;1] *> records_side rs.

(* Restore stops at the nearest six-zero separator.  Two-zero
   separators are paired returns; crossing one emits a whole record. *)
Fixpoint restored st rs :=
  match st with
  | SCap c=>cap_entry (cap_prefix c) (cap_height c) (records_side rs)
  | SPush true older ds n=>active older (RMore ds (2+n) rs)
  | SPush false older ds n=>restored older (RMore ds (2+n) rs)
  end.

Lemma emitted_good p ds n rs:
  Block p (ds,n) -> Good true rs ->
  Good (negb p) (RMore ds (2+n) rs).
Proof.
  intros HB HR; cbn [Good]; split; [apply emitted_segment; exact HB|].
  split; [destruct HB as [_ [H _]]; lia|exact HR].
Qed.

Lemma cap_emit c r:
  put_left (cap_word c) 0inf <{{A}} [1]^^8 *> r -->*
  cap_entry (cap_prefix c) (cap_height c) r.
Proof. destruct c; esx. Qed.

Lemma stack_return st rs:
  stack_good st -> Good true rs ->
  stack_side st <{{A}} [1]^^8 *> records_side rs -->* restored st rs.
Proof.
  gen rs; induction st as [c|six older IH ds n]; intros rs HL HR.
  - apply cap_emit.
  - destruct HL as [HL HB]; destruct six;
      cbn [stack_side restored]; follow (emit_block ds n).
    + assert (HZ:exists r, records_side (RMore ds (2+n) rs)=0 >> r).
      { eapply records_zero, emitted_good; eauto. }
      unfold active.
      destruct (stack_zero older) as [l E]; rewrite E.
      follow (return_six l _ HZ); finish.
    + follow (return_separator (stack_side older) _
        (records_zero true _ (emitted_good false ds n rs HB HR))).
      apply IH; [exact HL|apply (emitted_good false); assumption].
Qed.

Lemma restored_good st rs:
  stack_good st -> Good true rs ->
  (exists st' rs', restored st rs=active st' rs' /\
    stack_good st' /\ Good false rs' /\ stack_cap st'=stack_cap st /\
    stack_protected st' (first_digits rs')=stack_protected st (first_digits rs)) \/
  (exists rs', restored st rs=
    cap_entry (cap_prefix (stack_cap st)) (cap_height (stack_cap st))
      (records_side rs') /\ Good true rs' /\
    first_digits rs'=stack_protected st (first_digits rs)).
Proof.
  gen rs; induction st as [c|six older IH ds n]; intros rs HL HR.
  - right; exists rs; repeat split; assumption || reflexivity.
  - destruct HL as [HL HB]; destruct six.
    + left; exists older,(RMore ds (2+n) rs).
      split; [reflexivity|]; split; [exact HL|].
      split; [apply (emitted_good true); assumption|].
      split; reflexivity.
    + exact (IH _ HL (emitted_good false ds n rs HB HR)).
Qed.

Lemma carry_word u a l r:
  Forall (fun d=>d<=1) u -> a<=1 ->
  l |> digits (u++[a]) *> [0;0;0] *> r -->+
  l {{{ (hReturn,L) }}} digits (u++[1+a]) *> 0 >> r.
Proof.
  intros Hu Ha.
  rewrite !digits_app; cbn [digits flat_map]; repeat rewrite Str_app_assoc.
  follow10 (ordinary_return u a Hu Ha).
  change (l {{{ (hReturn,L) }}} 0 >> back_word u *>
    [0]^^(1+a) *> [1;1;0] *> r -->*
    l {{{ (hReturn,L) }}} digits u *> [0]^^(1+(1+a)) *> [1;1] *> 0 >> r).
  rewrite zero_back_word; finish.
Qed.

Lemma carry_inside u a n l r:
  Forall (fun d=>d<=1) u -> a<=1 ->
  l |> digits (u++[a;2]++repeat 0 n)%nat *> r -->+
  l {{{ (hReturn,L) }}} digits (u++[1+a;0]++repeat 0 n)%nat *> r.
Proof.
  intros Hu Ha.
  rewrite !digits_app; cbn [digits flat_map]; repeat rewrite Str_app_assoc.
  generalize (carry_word u a l ([1;1] *> digits (repeat 0%nat n) *> r) Hu Ha).
  rewrite !digits_app; cbn [digits flat_map]; repeat rewrite Str_app_assoc; auto.
Qed.

Lemma carry_blank u a l:
  Forall (fun d=>d<=1) u -> a<=1 ->
  l |> digits (u++[a]) *> 0inf -->+
  l {{{ (hReturn,L) }}} digits (u++[1+a]) *> 0inf.
Proof.
  intros Hu Ha; generalize (carry_word u a l 0inf Hu Ha).
  cbn [Str_app]; repeat rewrite <-const_unfold; auto.
Qed.

Lemma carry_records_spec rs rs':
  Advance rs [] rs' -> forall l,
  l |> records_side rs -->+ l {{{ (hReturn,L) }}} records_side rs'.
Proof.
  intro H; inversion H as [ds ds' HC|ds b ds' b' tail Hb HC|]; subst;
    intro l; cbn [records_side].
  - inverts HC; [apply carry_inside|apply carry_blank]; assumption.
  - inverts HC.
    + apply carry_inside; assumption.
    + match goal with H : ?b=0%nat \/ ?b=3%nat |- _ =>
        assert (b=3)%nat by lia; subst b end.
      apply carry_word; assumption.
Qed.

Lemma carry_records_good p rs rs':
  Advance rs [] rs' -> Good p rs -> Good (negb p) rs'.
Proof.
  intro H; inverts H; cbn [Good]; intro HG.
  - eapply carry_segment; eauto.
  - destruct HG as [HS [Hb HR]].
    split; [eapply carry_segment; eauto|].
    split; [eapply carry_header; eauto|exact HR].
Qed.

Lemma active_return st rs rs':
  stack_good st -> Good false rs -> Advance rs [] rs' ->
  active st rs -->+ restored st rs'.
Proof.
  intros HL HR HA.
  assert (HG:Good true rs') by (apply (carry_records_good false rs rs' HA HR)).
  unfold active; follow active_scan.
  follow10 (carry_records_spec rs rs' HA).
  follow (return_separator (stack_side st) _ (records_zero true rs' HG)).
  apply stack_return; assumption.
Qed.

Definition extend_stack bs st :=
  fold_left (fun st '(ds,n)=>SPush true st ds n) bs st.

Lemma extend_side bs st:
  stack_side (extend_stack bs st)=record_stack bs (stack_side st).
Proof.
  gen st; induction bs as [|[ds n] bs IH]; intro st; cbn [extend_stack record_stack].
  - reflexivity.
  - apply IH.
Qed.

Lemma extend_good bs st:
  Forall (Block true) bs -> stack_good st -> stack_good (extend_stack bs st).
Proof.
  intros H; gen st; induction H as [|[ds n] bs HB H IH]; intros st HL.
  - exact HL.
  - apply IH; split; assumption.
Qed.

Lemma extend_cap bs st: stack_cap (extend_stack bs st)=stack_cap st.
Proof.
  gen st; induction bs as [|[ds n] bs IH]; intro st; cbn [extend_stack].
  - reflexivity.
  - exact (IH (SPush true st ds n)).
Qed.

Lemma extend_protected bs st rs:
  stack_protected (extend_stack bs st) (first_digits rs)=
  stack_protected st (protected bs rs).
Proof.
  gen st; induction bs as [|[ds n] bs IH]; intro st;
    cbn [extend_stack protected]; [reflexivity|].
  exact (IH (SPush true st ds n)).
Qed.

Lemma active_constructor st ds b rs:
  stack_good st -> Segment false b ds -> Good true rs ->
  Forall (fun d=>d<=1) ds -> (b=1 \/ b=2)%nat ->
  exists st' rs', stack_good st' /\ Good false rs' /\
  stack_cap st'=stack_cap st /\
  stack_protected st' (first_digits rs')=stack_protected st ds /\
  (active st (RMore ds b rs) -->+ active st' rs').
Proof.
  intros HL HS HR HD Hb.
  destruct (advance_total rs HR) as [bs [rs' [HA [HB HG]]]].
  exists (extend_stack bs (SPush false st ds (b-1))),rs'.
  split.
  - apply extend_good; [exact HB|]; split; [exact HL|].
    eapply scanned_block; eauto.
  - split; [exact HG|]; split; [rewrite extend_cap; reflexivity|].
    split; [rewrite extend_protected; reflexivity|].
    unfold active; rewrite extend_side; cbn [records_side stack_side].
    follow active_scan.
    follow (scan_digits ds HD).
    destruct Hb; subst b;
      apply (advance_spec _ _ _ HA); auto.
Qed.

Open Scope nat_scope.

Definition Source st rs :=
  stack_good st /\ Good false rs /\
  measure (stack_protected st (first_digits rs))<=cap_bound (stack_cap st).

Lemma prefix_app n u v:
  n<=length u -> prefix_value n (u++v)=prefix_value n u.
Proof.
  gen n; induction u as [|d u IH]; intros [|n] H; cbn in *;
    try reflexivity; try lia; rewrite IH; [reflexivity|lia].
Qed.

Lemma measure_app u v:
  7<=length u -> measure (u++v)=measure u.
Proof.
  intro H; unfold measure; rewrite map_app; apply prefix_app.
  rewrite length_map; exact H.
Qed.

Lemma long_measure k:
  6<=k -> measure (2::repeat 0 k)=255.
Proof.
  intro H.
  replace k with (6+(k-6)) by lia.
  rewrite repeat_app.
  change (measure ((2::repeat 0 6)++repeat 0 (k-6))=255).
  rewrite measure_app; [reflexivity|reflexivity].
Qed.

Lemma long_segment b k:
  Segment false b (2::repeat 0 k) -> b<=3 ->
  (b=0 /\ Nat.odd k=true) \/ ((b=1 \/ b=3) /\ Nat.odd k=false).
Proof.
  intros [_ [_ [[HL HM] _]]] Hb.
  cbn [length mass] in *; rewrite repeat_length in HL; rewrite mass_zeros in HM.
  rewrite odd_next in HL.
  rewrite !Nat.odd_add in HM; cbn in HM.
  destruct b as [|[|[|[|b]]]]; try lia;
    destruct (Nat.odd k); cbn in *; intuition discriminate.
Qed.

Lemma source_long_marked st b k:
  Segment false b (2::repeat 0 k) ->
  measure (stack_protected st (2::repeat 0 k))<=cap_bound (stack_cap st) ->
  exists six older ds n, st=SPush six older ds n.
Proof.
  intros HS HM; destruct st as [c|six older ds n]; [|eauto].
  generalize (segment_length false b _ HS).
  cbn [length stack_protected stack_cap] in *; rewrite repeat_length.
  intro HK; rewrite long_measure in HM by lia.
  destruct c; cbn [cap_bound] in HM; lia.
Qed.

(* The long3 excursion appends one pending height3 and scans the
   ordinary prefix[1;0]++0^k.  Its whole effect on the last block is
   captured by this single binary payload, before the final carry. *)
Definition merged ds n k := ds++[n;1;1;0]++repeat 0 k.

Lemma merged_succ ds n k:
  merged ds n (1+k)=merged ds n k++[0].
Proof.
  unfold merged; rewrite <-!app_assoc.
  replace (1+k) with (k+1) by lia; rewrite repeat_app; reflexivity.
Qed.

Lemma zeros_binary k: Forall (fun d=>d<=1) (repeat 0 k).
Proof. induction k; constructor; auto; lia. Qed.

Lemma merged_binary ds n k:
  Forall (fun d=>d<=1) ds -> n<=1 ->
  Forall (fun d=>d<=1) (merged ds n k).
Proof.
  intros HD Hn; unfold merged; apply Forall_app; split; [exact HD|].
  apply Forall_app; split.
  - constructor; [exact Hn|]; repeat constructor; lia.
  - apply zeros_binary.
Qed.

Lemma merged_length ds n k: length (merged ds n k)=length ds+4+k.
Proof. unfold merged; rewrite !length_app, repeat_length; cbn; lia. Qed.

Lemma merged_mass ds n k: mass (merged ds n k)=mass ds+6+n+k.
Proof. unfold merged; rewrite !mass_app, mass_zeros; cbn [mass]; lia. Qed.

Lemma merged_segment p ds n b k:
  Block p (ds,n) -> Segment false b (2::repeat 0 k) ->
  Segment p b (merged ds n k).
Proof.
  intros [HD [Hn [HH [[HL HM] Hmin]]]] [_ [_ [[HK Hsum] _]]].
  cbn [Nat.add Nat.eqb] in HL.
  cbn [length mass] in HK,Hsum.
  rewrite repeat_length in HK; rewrite mass_zeros in Hsum.
  change (Nat.odd (3+k+b)=false) in Hsum.
  split; [apply num_binary, merged_binary; assumption|].
  split.
  - destruct ds; cbn [Head merged app] in *; [contradiction|].
    destruct HH as [H|[_ H]]; [left; exact H|discriminate].
  - split.
    + split.
      * rewrite merged_length, !Nat.odd_add, HL.
        cbn; rewrite odd_next in HK; exact HK.
      * replace (mass (merged ds n k)+b) with
          ((mass ds+(1+n))+(2+(3+k+b))) by (rewrite merged_mass; lia).
        rewrite Nat.odd_add, HM, Nat.odd_add, Hsum; cbn.
        apply Bool.xorb_false_r.
    + rewrite merged_length; destruct (b=?0); lia.
Qed.

Lemma merged_block p ds n k:
  Block p (ds,n) -> Segment false 1 (2::repeat 0 k) ->
  Block p (merged ds n k,0).
Proof.
  intros HB HS; apply (scanned_block p 1); [| |auto].
  - eapply merged_segment; eauto.
  - apply merged_binary; destruct HB as [HD [Hn _]]; assumption.
Qed.

Lemma merged_bump_segment p ds n b k:
  Block p (ds,n) -> Segment false b (2::repeat 0 (1+k)) ->
  (b=0 \/ b=3) ->
  Segment (negb p) (b-2) (merged ds n k++[1]).
Proof.
  intros HB HS Hb; apply (segment_last p b (merged ds n k) 0).
  - apply merged_binary; destruct HB as [HD [Hn _]]; assumption.
  - lia.
  - rewrite <-merged_succ; eapply merged_segment; eauto.
  - exact Hb.
Qed.

Lemma stack_measure st u v:
  measure u=measure v ->
  measure (stack_protected st u)=measure (stack_protected st v).
Proof. destruct st; cbn; auto. Qed.

Lemma merged_measure ds n k:
  7<=length ds -> measure (merged ds n k)=measure ds.
Proof. apply measure_app. Qed.

Lemma bumped_measure ds n k:
  7<=length ds -> measure (merged ds n k++[1])=measure ds.
Proof. unfold merged; rewrite <-!app_assoc; apply measure_app. Qed.

Lemma initial_source:
  Source (SCap C0) (REnd (seed_offset++[1])).
Proof.
  split; [exact I|]; split.
  - split; [apply num_binary; repeat constructor; lia|].
    unfold seed_offset, Head, Tags; cbn [app length mass]; repeat split; auto; lia.
  - reflexivity.
Qed.

Open Scope sym_scope.

Lemma pending_app u v l: pending (u++v) l=pending v (pending u l).
Proof. apply fold_left_app. Qed.

Lemma merged_pending ds n k l:
  pending (merged ds n k) l=
  pending ([1;0]++repeat 0 k)%nat
    (pending ds l <* [1]^^(2+n) <* [0] <* [1]^^3 <* [0]).
Proof. unfold merged; rewrite !pending_app; reflexivity. Qed.

Lemma long_scan k l r:
  l <* [1] |> [0;0;1;1;1] *> digits (2::repeat 0 k)%nat *> r -->+
  pending ([1;0]++repeat 0 k)%nat (l <* [1]^^3 <* [0]) |> r.
Proof.
  follow10 active_turn.
  apply (scan_digits ([1;0]++repeat 0 k)%nat).
  constructor; [lia|]; constructor; [lia|apply zeros_binary].
Qed.

Lemma long_pending ds n k l r:
  pending ds l <* [1]^^(2+n) <* [0] <* [1] |>
    [0;0;1;1;1] *> digits (2::repeat 0 k)%nat *> r -->+
  pending (merged ds n k) l |> r.
Proof. rewrite merged_pending; apply long_scan. Qed.

Lemma pending_carry u a l r:
  pending (u++[a]) l |> [0;0;0] *> r -->+
  l {{{ (hReturn,L) }}} digits (u++[1+a]) *> 0 >> r.
Proof.
  rewrite pending_app; cbn [pending fold_left].
  follow10 (start_back a).
  follow (pending_back u).
  change (l {{{ (hReturn,L) }}} 0 >> back_word u *>
    [0]^^(1+a) *> [1;1;0] *> r -->*
    l {{{ (hReturn,L) }}} digits (u++[1+a]) *> 0 >> r).
  rewrite zero_back_word, digits_app; cbn [digits flat_map].
  repeat rewrite Str_app_assoc; finish.
Qed.

Lemma long_pending_return ds n k l r:
  pending ds l <* [1]^^(2+n) <* [0] <* [1] |>
    [0;0;1;1;1] *> digits (2::repeat 0 (1+k))%nat *> [0;0;0] *> r -->+
  l {{{ (hReturn,L) }}} digits (merged ds n k++[1])%nat *> 0 >> r.
Proof.
  follow11 (long_pending ds n (1+k)).
  rewrite merged_succ; apply pending_carry.
Qed.

Lemma long_pending_blank ds n k l:
  pending ds l <* [1]^^(2+n) <* [0] <* [1] |>
    [0;0;1;1;1] *> digits (2::repeat 0 (1+k))%nat *> 0inf -->+
  l {{{ (hReturn,L) }}} digits (merged ds n k++[1])%nat *> 0inf.
Proof.
  generalize (long_pending_return ds n k l 0inf).
  cbn [Str_app]; repeat rewrite <-const_unfold; auto.
Qed.

Definition return_to (six:bool) older rs :=
  if six then active older rs else restored older rs.

Lemma finish_return six older rs:
  stack_good older -> Good (negb six) rs ->
  (if six then stack_side older <* [0]^^5
     else stack_side older <* [1]^^4 <* [0;0])
    {{{ (hReturn,L) }}} records_side rs -->* return_to six older rs.
Proof.
  intros HL HR; destruct six; cbn [return_to].
  - unfold active; destruct (stack_zero older) as [l E]; rewrite E.
    apply (return_six l _ (records_zero false rs HR)).
  - follow (return_separator (stack_side older) _ (records_zero true rs HR)).
    apply stack_return; assumption.
Qed.

Inductive Ready : (Q*tape)%type -> Prop :=
| ReadyP st rs: Source st rs -> Ready (active st rs)
| ReadyCap c rs: Good true rs ->
    measure (first_digits rs)<=1+cap_bound c ->
    Ready (cap_entry (cap_prefix c) (cap_height c) (records_side rs)).

Lemma cap_progress c rs:
  Good true rs -> measure (first_digits rs)<=1+cap_bound c ->
  exists q, Ready q /\
    (cap_entry (cap_prefix c) (cap_height c) (records_side rs) -->+ q).
Proof.
  intros HR HM; destruct (cap_rule c rs HR HM) as [bs [rs' [HB [HG [HV HS]]]]].
  exists (active (extend_stack bs (SCap (next_cap c))) rs'); split.
  - constructor; split; [apply extend_good; [exact HB|exact I]|].
    split; [exact HG|]; rewrite extend_protected, extend_cap; exact HV.
  - unfold active; rewrite extend_side; exact HS.
Qed.

Lemma restored_ready st rs:
  stack_good st -> Good true rs ->
  measure (stack_protected st (first_digits rs))<=cap_bound (stack_cap st) ->
  Ready (restored st rs).
Proof.
  intros HL HR HM.
  destruct (restored_good st rs HL HR)
    as [[st' [rs' [E [HL' [HR' [HC HP]]]]]]|[rs' [E [HR' HP]]]];
    rewrite E.
  - constructor; split; [exact HL'|]; split; [exact HR'|].
    rewrite HC, HP; exact HM.
  - constructor; [exact HR'|]; rewrite HP; lia.
Qed.

Lemma carry_records_bound p rs rs':
  Advance rs [] rs' -> Good p rs ->
  measure (first_digits rs')<=1+measure (first_digits rs).
Proof.
  intro H; inverts H; cbn [Good first_digits]; intro HG.
  - eapply carry_bound; [eassumption|eapply segment_length; eauto].
  - destruct HG as [HS _].
    eapply carry_bound; [eassumption|eapply segment_length; eauto].
Qed.

Lemma ordinary_progress st rs rs':
  Source st rs -> Advance rs [] rs' ->
  Ready (restored st rs') /\ (active st rs -->+ restored st rs').
Proof.
  intros [HL [HR HM]] HA; split; [|apply active_return; assumption].
  assert (HG:Good true rs') by (apply (carry_records_good false rs rs' HA HR)).
  destruct st as [c|six older ds n].
  - constructor; [exact HG|].
    generalize (carry_records_bound false rs rs' HA HR).
    cbn [stack_protected stack_cap] in HM; lia.
  - apply restored_ready; assumption.
Qed.

Lemma constructor_progress st ds b rs:
  Source st (RMore ds b rs) -> Forall (fun d=>d<=1) ds ->
  (b=1 \/ b=2)%nat ->
  exists q, Ready q /\ (active st (RMore ds b rs) -->+ q).
Proof.
  intros [HL [[HS [Hb HR]] HM]] HD HB.
  destruct (active_constructor st ds b rs HL HS HR HD HB)
    as [st' [rs' [HL' [HR' [HC [HP HT]]]]]].
  exists (active st' rs'); split; [|exact HT].
  constructor; split; [exact HL'|]; split; [exact HR'|].
  rewrite HC, HP; exact HM.
Qed.

Lemma return_to_ready six older rs:
  stack_good older -> Good (negb six) rs ->
  measure (stack_protected older (first_digits rs))<=cap_bound (stack_cap older) ->
  Ready (return_to six older rs).
Proof.
  intros HL HR HM; destruct six; cbn [return_to].
  - constructor; repeat split; assumption.
  - apply restored_ready; assumption.
Qed.

Lemma long_constructor_progress six older ds n k rs:
  Source (SPush six older ds n) (RMore (2::repeat 0 k)%nat 1 rs) ->
  exists q, Ready q /\
    (active (SPush six older ds n) (RMore (2::repeat 0 k)%nat 1 rs) -->+ q).
Proof.
  intros [[HL HB] [[HS [_ HR]] HM]].
  destruct (advance_total rs HR) as [bs [rs' [HA [HBs HG]]]].
  exists (active (extend_stack bs (SPush six older (merged ds n k) 0)) rs').
  split.
  - constructor; split.
    + apply extend_good; [exact HBs|]; split; [exact HL|].
      eapply merged_block; eauto.
    + split; [exact HG|]; rewrite extend_cap, extend_protected.
      cbn [stack_cap stack_protected].
      rewrite (stack_measure older _ ds
        (merged_measure ds n k (block_length six ds n HB))).
      exact HM.
  - unfold active; rewrite extend_side; cbn [stack_side records_side].
    follow11 (long_pending ds n k).
    apply (advance_spec _ _ _ HA); auto.
Qed.

Lemma long_end_progress six older ds n k:
  Source (SPush six older ds n) (REnd (2::repeat 0 (1+k))%nat) ->
  exists q, Ready q /\
    (active (SPush six older ds n) (REnd (2::repeat 0 (1+k))%nat) -->+ q).
Proof.
  intros [[HL HB] [HS HM]].
  assert (HG:Good (negb six) (REnd (merged ds n k++[1])%nat)).
  { apply (merged_bump_segment six ds n 0); auto. }
  exists (return_to six older (REnd (merged ds n k++[1])%nat)); split.
  - apply return_to_ready; [exact HL|exact HG|].
    cbn [first_digits].
    rewrite (stack_measure older _ ds
      (bumped_measure ds n k (block_length six ds n HB))).
    exact HM.
  - unfold active; cbn [stack_side records_side].
    follow10 (long_pending_blank ds n k).
    exact (finish_return six older (REnd (merged ds n k++[1])%nat) HL HG).
Qed.

Lemma long_three_progress six older ds n k rs:
  Source (SPush six older ds n) (RMore (2::repeat 0 (1+k))%nat 3 rs) ->
  exists q, Ready q /\
    (active (SPush six older ds n) (RMore (2::repeat 0 (1+k))%nat 3 rs) -->+ q).
Proof.
  intros [[HL HB] [[HS [_ HR]] HM]].
  assert (HG:Good (negb six) (RMore (merged ds n k++[1])%nat 1 rs)).
  { split; [apply (merged_bump_segment six ds n 3); auto|].
    split; [lia|exact HR]. }
  exists (return_to six older (RMore (merged ds n k++[1])%nat 1 rs)); split.
  - apply return_to_ready; [exact HL|exact HG|].
    cbn [first_digits].
    rewrite (stack_measure older _ ds
      (bumped_measure ds n k (block_length six ds n HB))).
    exact HM.
  - unfold active; cbn [stack_side records_side].
    follow10 (long_pending_return ds n k).
    exact (finish_return six older (RMore (merged ds n k++[1])%nat 1 rs) HL HG).
Qed.

Lemma source_progress st rs:
  Source st rs -> exists q, Ready q /\ (active st rs -->+ q).
Proof.
  intro H; destruct rs as [ds|ds b rs].
  - destruct (proj2 H) as [HS HM].
    destruct (segment_progress 0 ds HS ltac:(lia))
      as [[k E]|[[ds' [b' HC]]|[_ Hb]]].
    + subst ds.
      destruct (source_long_marked st 0 k HS HM) as [six [older [ds [n E]]]].
      subst st; destruct k as [|k].
      * generalize (segment_length false 0 _ HS); cbn; lia.
      * apply long_end_progress; exact H.
    + apply carry_zero in HC as E; subst b'.
      exists (restored st (REnd ds')); apply ordinary_progress; [exact H|].
      constructor; exact HC.
    + lia.
  - destruct (proj2 H) as [[HS [Hb HR]] HM].
    destruct (segment_progress b ds HS (proj2 Hb))
      as [[k E]|[[ds' [b' HC]]|[HD HB]]].
    + subst ds.
      destruct (source_long_marked st b k HS HM) as [six [older [ds [n E]]]].
      subst st.
      destruct (long_segment b k HS (proj2 Hb)) as [[E _]|[[E|E] _]];
        subst b; [lia|apply long_constructor_progress; exact H|].
      destruct k as [|k].
      * generalize (segment_length false 3 _ HS); cbn; lia.
      * apply long_three_progress; exact H.
    + exists (restored st (RMore ds' b' rs)); apply ordinary_progress; [exact H|].
      constructor; [lia|exact HC].
    + apply constructor_progress; assumption.
Qed.

Lemma ready_progress q:
  Ready q -> exists q', Ready q' /\ (q -->+ q').
Proof.
  intro H; destruct H; [apply source_progress|apply cap_progress]; assumption.
Qed.

Lemma source_nonhalt st rs:
  Source st rs -> ~halts tm (active st rs).
Proof.
  intro H; eapply progress_nonhalt with (P:=Ready).
  - apply ready_progress.
  - constructor; exact H.
Qed.

Lemma init:
  c0 -->* put_left [4] 0inf <* [1] |>
    [0;0;1;1;1] *> payload (seed++[2]) *> 0inf.
Proof. esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply (source_nonhalt (SCap C0) (REnd (seed_offset++[1])%nat)).
  exact initial_source.
Qed.

End TM24.

Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC0LF_0LD0RC_1RA1LD_1LB0LE_---0RE").

Definition state_map q :=
  match q with A=>B | B=>C | C=>D | D=>A | E=>E | F=>F end.

Lemma permutation: Perm tm TM24.tm state_map.
Proof.
  split; intros [] []; cbn; intros; try reflexivity; try discriminate;
    match goal with H: Some _=Some _ |- _ => inversion H; reflexivity end.
Qed.

Definition init_left :=
  TM24.put_left [3;3;2;3;3;3;2;3]
    (TM24.put_left [4;3;3;2;2;2] 0inf <* [1]^^4 <* [0;0]).
Definition init_right :=
  [0;0;1;1;1] *>
  TM24.payload [2;2;2;1;1;1;1;1;2;2;1;1;1;1;1;2]%nat *> 0inf.

Definition entry_stack :=
  TM24.SPush false (TM24.SCap TM24.C2) [1;1;0;1;1;1;0]%nat 1.
Definition entry_records :=
  TM24.REnd [1;1;1;0;0;0;0;0;1;1;0;0;0;0;0;1]%nat.

Lemma entry_source: TM24.Source entry_stack entry_records.
Proof.
  split.
  - split; [exact I|]; repeat split; repeat constructor; lia.
  - split.
    + split; [apply TM24.num_binary; repeat constructor; lia|].
      unfold TM24.Head, TM24.Tags; repeat split; repeat constructor; lia.
    + cbn [entry_stack entry_records TM24.stack_protected TM24.first_digits
        TM24.stack_cap TM24.cap_bound TM24.measure TM24.prefix_value map Nat.pow];
        lia.
Qed.

Lemma mapped_entry:
  init_left <* <[1;0] {{D}}> init_right=TM24.active entry_stack entry_records.
Proof. reflexivity. Qed.

Lemma init:
  c0 -[tm]->* init_left <* <[1;0] {{C}}> init_right.
Proof. esx. Qed.

Lemma nonhalt_of_entry:
  ~halts TM24.tm (init_left <* <[1;0] {{D}}> init_right) ->
  ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply init|].
  eapply perm_nonhalt; [apply permutation|exact H].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply nonhalt_of_entry; rewrite mapped_entry.
  apply TM24.source_nonhalt, entry_source.
Qed.

End TM25.
