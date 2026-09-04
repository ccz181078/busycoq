From BusyCoq Require Import Individual62.

Require Import PeanoNat ZifyNat Lia String List.
From BusyCoq Require Import Longitudinal ES_v3.

Import ListNotations.
Open Scope list_scope.

Ltac es_v3_pre ::= ut.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1LA_1RC1LE_1RA1RD_1RC0RF_---0LA_1RA0RA").

Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Definition h1:list(DH0*DH0) := [((A,<[1;1;0;0]),(A,[]))].
Definition D1 n := [0;1;1]++[1;1]^^n.
Definition D2 n := [0;1]++[1;1]^^n.

Lemma D1_Inc n: segRLs tm h1 h1 (D1 n) (D1 n).
Proof. esx. Qed.

Lemma rh_Inc: sideRLs tm h1 0inf (D1 1 *> D1 0 *> 0inf).
Proof. esx. Qed.

Lemma D21_Inc n m r:
  sideRLs tm h1 (D2 n *> D1 m *> r) (D1 n *> D2(2+m) *> r).
Proof. es' n m & r. Qed.

Lemma D22_Inc n m r:
  sideRLs tm h1 (D2 n *> D2 m *> r) (D1 n *> D1(1+m) *> r).
Proof. es' n m & r. Qed.

Definition S' '(n,r) :=
  0inf <* <[1;1]^^n {{{ (A,<[1;1;0;0],R) }}} r.

Lemma Inc n r r':
  sideRLs tm h1 r r' -> S'(1+n,r) -->+ S'(n,r').
Proof.
  unfold S'. intros H.
  eapply sideRLs_1 in H.
  follow10 H. es' n & r'.
Qed.

Lemma Ov n m r r':
  sideRLs tm h1 r (D1 n *> D1 m *> r') ->
  S'(O,r) -->+ S'(n,D2(2+m) *> r').
Proof.
  unfold S'. intros H.
  eapply sideRLs_1 in H.
  follow10 H. es' n m & r'.
Qed.

Lemma init:
  c0 -->* S'(O,D1 3 *> (D1 1++D1 0)^^3 *> 0inf).
Proof. esx. Qed.

Inductive word := W1(n:nat) | W2(n:nat).

Definition word_side w r :=
  match w with W1 n => D1 n *> r | W2 n => D2 n *> r end.

Fixpoint words_side ws:side :=
  match ws with [] => 0inf | w::ws => word_side w (words_side ws) end.

Fixpoint signal ws:option(list word) :=
  match ws with
  | [] => Some[W1 1;W1 0]
  | W1 n::ws =>
      match signal ws with Some ws' => Some(W1 n::ws') | None => None end
  | W2 _::[] => None
  | W2 n::W1 m::ws => Some(W1 n::W2(2+m)::ws)
  | W2 n::W2 m::ws => Some(W1 n::W1(1+m)::ws)
  end.

Fixpoint signals k ws:option(list word) :=
  match k with
  | O => Some ws
  | S k => match signal ws with Some ws' => signals k ws' | None => None end
  end.

Definition reset ws:option(list word) :=
  match signal ws with
  | Some(W1 a::W1 b::ws') => signals a (W2(2+b)::ws')
  | _ => None
  end.

Definition double_reset ws :=
  match reset ws with Some ws' => reset ws' | None => None end.

Lemma signal_sound ws ws':
  signal ws=Some ws' -> sideRLs tm h1 (words_side ws) (words_side ws').
Proof.
  revert ws'.
  induction ws as [|[n|n] ws IH]; intros ws'; cbn.
  - intros[= <-]. exact rh_Inc.
  - destruct(signal ws) as [ws0|] eqn:E; try discriminate.
    intros[= <-]. cbn.
    change (sideRLs tm h1 (D1 n *> words_side ws)
      (D1 n *> words_side ws0)).
    eapply segRLs_sideRLs_concat; [apply D1_Inc|apply IH; reflexivity].
  - destruct ws as [|[m|m] ws]; cbn; try discriminate.
    + intros[= <-].
      change (sideRLs tm h1 (D2 n *> D1 m *> words_side ws)
        (D1 n *> D2(2+m) *> words_side ws)).
      apply D21_Inc.
    + intros[= <-].
      change (sideRLs tm h1 (D2 n *> D2 m *> words_side ws)
        (D1 n *> D1(1+m) *> words_side ws)).
      apply D22_Inc.
Qed.

Lemma signals_sound k ws ws':
  signals k ws=Some ws' ->
  sideRLs tm (h1^^k) (words_side ws) (words_side ws').
Proof.
  revert ws ws'.
  induction k as [|k IH]; intros ws ws'; cbn.
  - intros[= <-]. constructor.
  - destruct(signal ws) as [ws0|] eqn:E; try discriminate.
    intros H.
    change (sideRLs tm (h1++h1^^k) (words_side ws) (words_side ws')).
    eapply sideRLs_trans; [apply signal_sound,E|apply IH,H].
Qed.

Lemma countdown n r r':
  sideRLs tm (h1^^n) r r' -> S'(n,r) -->* S'(O,r').
Proof.
  revert r r'.
  induction n as [|n IH]; intros r r' H.
  - cbn in H. inverts H. constructor.
  - change (sideRLs tm (h1++h1^^n) r r') in H.
    apply sideRLs_split in H as [r0[H0 H]].
    eapply evstep_trans.
    + apply progress_evstep,Inc,H0.
    + apply IH,H.
Qed.

Lemma reset_sound ws ws':
  reset ws=Some ws' ->
  S'(O,words_side ws) -->+ S'(O,words_side ws').
Proof.
  unfold reset.
  destruct(signal ws) as [ws0|] eqn:E; try discriminate.
  destruct ws0 as [|[a|a] ws0]; try discriminate.
  destruct ws0 as [|[b|b] ws0]; try discriminate.
  intros H.
  eapply progress_evstep_trans.
  - eapply Ov.
    pose proof (signal_sound _ _ E) as HE.
    change (sideRLs tm h1 (words_side ws)
      (D1 a *> D1 b *> words_side ws0)) in HE.
    exact HE.
  - eapply countdown.
    pose proof (signals_sound a (W2(2+b)::ws0) ws' H) as HH.
    change (sideRLs tm (h1^^a)
      (D2(2+b) *> words_side ws0) (words_side ws')) in HH.
    exact HH.
Qed.

Lemma double_reset_sound ws ws':
  double_reset ws=Some ws' ->
  S'(O,words_side ws) -->+ S'(O,words_side ws').
Proof.
  unfold double_reset.
  destruct(reset ws) as [ws0|] eqn:E; try discriminate.
  intros H.
  eapply progress_evstep_trans.
  - apply reset_sound,E.
  - apply progress_evstep,reset_sound,H.
Qed.

Lemma signal_prefix xs ws:
  signal(map W1 xs++ws)=
  match signal ws with
  | Some ws' => Some(map W1 xs++ws')
  | None => None
  end.
Proof.
  induction xs as [|x xs IH].
  - cbn. destruct(signal ws); reflexivity.
  - cbn. rewrite IH. destruct(signal ws); reflexivity.
Qed.

Lemma signals_prefix k xs ws:
  signals k (map W1 xs++ws)=
  match signals k ws with
  | Some ws' => Some(map W1 xs++ws')
  | None => None
  end.
Proof.
  revert xs ws.
  induction k as [|k IH]; intros xs ws; cbn; auto.
  rewrite signal_prefix.
  destruct(signal ws); cbn; auto.
Qed.

Lemma signal_all xs:
  signal(map W1 xs)=Some(map W1 (xs++[1%nat;0%nat])).
Proof.
  rewrite <-app_nil_r at 1.
  rewrite signal_prefix. cbn. now rewrite map_app.
Qed.

Lemma signals_all k xs:
  signals k (map W1 xs)=Some(map W1 (xs++[1%nat;0%nat]^^k)).
Proof.
  revert xs.
  induction k as [|k IH]; intros xs; cbn.
  - now rewrite app_nil_r.
  - rewrite signal_all,IH.
    now rewrite <-app_assoc.
Qed.

Lemma signals_sweep n xs z tail:
  signals (S(length xs))
    (W2 n::(map W1 xs++W1 z::tail))=
  Some(map W1 (n::map (fun x => x+2) xs)++W2(z+2)::tail).
Proof.
  revert n.
  induction xs as [|x xs IH]; intros n.
  - cbn. replace (S(S z)) with (z+2) by lia. reflexivity.
  - change (signals (S(length xs))
      (W1 n::W2(2+x)::map W1 xs++W1 z::tail)=
      Some(W1 n::W1(x+2)::map W1(map (fun y => y+2) xs)++
        W2(z+2)::tail)).
    change (signals (S(length xs))
      (map W1[n]++W2(2+x)::map W1 xs++W1 z::tail)=
      Some(W1 n::W1(x+2)::map W1(map (fun y => y+2) xs)++
        W2(z+2)::tail)).
    rewrite signals_prefix,IH.
    cbn. replace (S(S x)) with (x+2) by lia. reflexivity.
Qed.

Lemma signals_add k l ws:
  signals(k+l) ws=
  match signals k ws with Some ws' => signals l ws' | None => None end.
Proof.
  revert ws.
  induction k as [|k IH]; intros ws; cbn; auto.
  destruct(signal ws); cbn; auto.
Qed.

Lemma signals_collision n xs z m tail:
  signals (S(S(length xs)))
    (W2 n::(map W1 xs++W1 z::W2 m::tail))=
  Some(map W1 (n::map (fun x => x+2) xs++[z+2;m+1])++tail).
Proof.
  replace (S(S(length xs))) with (S(length xs)+1) by lia.
  rewrite signals_add,signals_sweep.
  cbn.
  rewrite signal_prefix. cbn.
  rewrite map_app. cbn.
  replace (S m) with (m+1) by lia.
  f_equal. now rewrite <-app_assoc.
Qed.

Lemma signal_move_prefix xs n m tail:
  signal(map W1 xs++W2 n::W1 m::tail)=
  Some(map W1 xs++W1 n::W2(2+m)::tail).
Proof. rewrite signal_prefix. reflexivity. Qed.

Lemma double_formula b x xs z v tail m:
  b+2=2+length xs+m ->
  double_reset
    (map W1 ([2+length xs;b]++(x::xs++[z])++v::tail))=
  Some(map W1
    (map (fun n => n+4) (x::xs++[z])++
      (v+3)::tail++[1%nat;0%nat]^^S m)).
Proof.
  intros Hm.
  unfold double_reset.
  unfold reset at 1.
  rewrite signal_all.
  rewrite !map_app.
  cbn [map app].
  replace (2+length xs) with (S(length(x::xs))) by (cbn; lia).
  rewrite <-app_assoc.
  rewrite !map_app.
  cbn [map app].
  repeat rewrite <-app_assoc.
  change
    (match signals (S(length(x::xs)))
      (W2(2+b)::(map W1(x::xs)++W1 z::
        (W1 v::map W1 tail++[W1 1;W1 0]))) with
     | Some ws' => reset ws'
     | None => None
     end = Some
       (W1(x+4)::map W1(map (fun n => n+4) xs)++[W1(z+4)]++
         W1(v+3)::map W1 tail++map W1([1%nat;0%nat]^^S m))).
  rewrite (signals_sweep (2+b) (x::xs) z
    (W1 v::map W1 tail++[W1 1;W1 0])).
  unfold reset.
  change
    (match signal
      (map W1(2+b::map (fun n => n+2) (x::xs))++
        W2(z+2)::W1 v::(map W1 tail++[W1 1;W1 0])) with
     | Some(W1 a::W1 b0::ws') => signals a (W2(2+b0)::ws')
     | _ => None
     end = Some
       (W1(x+4)::map W1(map (fun n => n+4) xs)++[W1(z+4)]++
         W1(v+3)::map W1 tail++map W1([1%nat;0%nat]^^S m))).
  rewrite signal_move_prefix.
  cbn [map app].
  replace (2+b) with (S(S(length xs))+m) by lia.
  rewrite signals_add.
  replace (2+(x+2)) with (x+4) by lia.
  replace (2+v) with (v+2) by lia.
  replace (S(S(length xs))) with
    (S(S(length(map (fun n => n+2) xs)))) by now rewrite length_map.
  rewrite (signals_collision (x+4) (map (fun n => n+2) xs)
    (z+2) (v+2) (map W1 tail++[W1 1;W1 0])).
  cbn.
  replace
    (W1(x+4)::
      map W1(map (fun x => x+2) (map (fun n => n+2) xs)++
        [z+2+2;v+2+1])++map W1 tail++[W1 1;W1 0]) with
    (map W1((x+4)::
      (map (fun x => x+2) (map (fun n => n+2) xs)++
        [z+2+2;v+2+1])++tail++[1%nat;0%nat])) by
      (cbn [map]; rewrite !map_app; repeat rewrite <-app_assoc; reflexivity).
  rewrite signals_all.
  f_equal.
  rewrite !map_app.
  cbn [map app].
  rewrite !map_app.
  assert (Hmap:
    map W1(map (fun x => x+2) (map (fun n => n+2) xs))=
    map W1(map (fun n => n+4) xs)).
  { rewrite !map_map. apply map_ext. intros q. f_equal. lia. }
  rewrite Hmap.
  replace (z+2+2) with (z+4) by lia.
  replace (v+2+1) with (v+3) by lia.
  repeat rewrite <-app_assoc.
  reflexivity.
Qed.

Inductive letter := LA | LB | LC | LD | LE.
Inductive edge := EA | ED.

Definition ltotal (l:letter):nat :=
  match l with LA => 0 | LB => 1 | LC => 4 | LD => 3 | LE => 4 end.

Definition phase (l:letter):nat :=
  match l with LD | LE => 1 | _ => 0 end.

Definition edge_total (e:edge):nat := match e with EA => 0 | ED => 3 end.

Fixpoint total (ls:list letter):nat :=
  match ls with [] => 0 | l::ls => ltotal l+total ls end.

Definition pair_cells (l:letter) (q:nat):list nat :=
  match l with
  | LA => [q;q+1]
  | LB => [q+1;q+2]
  | LC => [q+4;q+4]
  | LD => [q+3;q+1]
  | LE => [q+4;q+2]
  end.

Fixpoint cells (ls:list letter) (q:nat):list nat :=
  match ls with
  | [] => []
  | l::ls => pair_cells l (total ls+q)++cells ls q
  end.

Definition right_letters (e:edge) (r:nat):list letter :=
  match e with EA => [LA]^^r | ED => LD::[LA]^^r end.

Definition numbers (e:edge) (left:list letter) (r:nat):list nat :=
  cells (left++right_letters e r) 0++[0%nat].

Definition State '(e,left,r) := S'(O,words_side(map W1(numbers e left r))).

Lemma total_app xs ys: total(xs++ys)=total xs+total ys.
Proof. induction xs; cbn; lia. Qed.

Lemma total_A_pow r: total([LA]^^r)=0%nat.
Proof. induction r; cbn; auto. Qed.

Lemma cells_app xs ys q:
  cells(xs++ys) q=cells xs (total ys+q)++cells ys q.
Proof.
  induction xs as [|x xs IH]; cbn; auto.
  rewrite total_app,IH.
  replace (total xs+total ys+q) with (total xs+(total ys+q)) by lia.
  now rewrite <-app_assoc.
Qed.

Lemma pair_cells_add l q k:
  pair_cells l (q+k)=map (fun n => n+k) (pair_cells l q).
Proof.
  destruct l; cbn [pair_cells map].
  - f_equal. f_equal. lia.
  - f_equal; [lia|]. f_equal. lia.
  - f_equal; [lia|]. f_equal. lia.
  - f_equal; [lia|]. f_equal. lia.
  - f_equal; [lia|]. f_equal. lia.
Qed.

Lemma cells_add xs q k:
  cells xs (q+k)=map (fun n => n+k) (cells xs q).
Proof.
  induction xs as [|x xs IH]; cbn; auto.
  replace (total xs+(q+k)) with ((total xs+q)+k) by lia.
  rewrite pair_cells_add,IH,map_app. reflexivity.
Qed.

Lemma cells_length xs q: length(cells xs q)=2*length xs.
Proof.
  induction xs as [|x xs IH]; cbn [cells]; auto.
  rewrite length_app,IH. destruct x; cbn [pair_cells length]; lia.
Qed.

Lemma cells_A_pow r: cells([LA]^^r) 0%nat=[0%nat;1%nat]^^r.
Proof.
  induction r; cbn [lpow cells pair_cells total]; auto.
  rewrite cells_app,total_A_pow,IHr. reflexivity.
Qed.

Lemma numbers_EA left r:
  numbers EA left r=cells left 0%nat++[0%nat;1%nat]^^r++[0%nat].
Proof.
  unfold numbers,right_letters.
  rewrite cells_app,total_A_pow,cells_A_pow. cbn.
  now rewrite <-app_assoc.
Qed.

Lemma numbers_ED left r:
  numbers ED left r=cells left 3%nat++[3%nat;1%nat]++
    [0%nat;1%nat]^^r++[0%nat].
Proof.
  unfold numbers,right_letters.
  rewrite cells_app. cbn [total]. rewrite total_A_pow.
  cbn [ltotal cells pair_cells]. rewrite total_A_pow,cells_A_pow. cbn.
  repeat rewrite <-app_assoc. reflexivity.
Qed.

Lemma double_formula_last b pre z v tail m:
  pre<>[] -> b+2=S(length pre)+m ->
  double_reset
    (map W1([S(length pre);b]++pre++[z]++v::tail))=
  Some(map W1
    (map (fun n => n+4) (pre++[z])++
      (v+3)::tail++[1%nat;0%nat]^^S m)).
Proof.
  destruct pre as [|x xs]; [congruence|]. intros _ Hm.
  cbn [length] in *.
  replace (S(S(length xs))) with (2+length xs) by lia.
  repeat rewrite <-app_assoc.
  rewrite (app_assoc (x::xs) [z] (v::tail)).
  apply double_formula. lia.
Qed.

Lemma A_stream r:
  [0%nat;1%nat]^^r++[0%nat]=0%nat::[1%nat;0%nat]^^r.
Proof.
  induction r; cbn [lpow]; auto.
  repeat rewrite <-app_assoc. cbn. now rewrite IHr.
Qed.

Lemma A_stream_two k:
  [0%nat;1%nat]^^S(S k)++[0%nat]=
  [0%nat;1%nat;0%nat]++[1%nat;0%nat]^^S k.
Proof. rewrite A_stream. reflexivity. Qed.

Lemma regroup_010 a b xs tail:
  ([a;b]++xs)++[0%nat;1%nat;0%nat]++tail=
  [a;b]++(xs++[0%nat])++[1%nat]++0%nat::tail.
Proof. repeat rewrite <-app_assoc. reflexivity. Qed.

Lemma regroup_c10' a b xs c tail:
  ([a;b]++xs)++[c;1%nat]++0%nat::tail=
  [a;b]++(xs++[c])++[1%nat]++0%nat::tail.
Proof. repeat rewrite <-app_assoc. reflexivity. Qed.

Lemma regroup_odd a b xs k:
  ([a;b]++xs)++0%nat::[1%nat;0%nat]^^S(S k)=
  [a;b]++xs++[0%nat]++1%nat::0%nat::[1%nat;0%nat]^^S k.
Proof. cbn [lpow app]. repeat rewrite <-app_assoc. reflexivity. Qed.

Lemma suffix_EA_A k:
  4%nat::5%nat::3%nat::
    ([1%nat;0%nat]^^S k++[1%nat;0%nat]^^4)=
  cells [LB;LD;LA] 0%nat++
    [0%nat;1%nat]^^(S(S k)+1)++[0%nat].
Proof.
  rewrite A_stream.
  cbn [cells total ltotal pair_cells map app].
  repeat rewrite <-app_assoc.
  repeat rewrite <-lpow_add.
  cbn [Nat.add]. do 3 f_equal.
  change ([1%nat;0%nat]^^(S k+4)=
    [1%nat;0%nat]^^2++[1%nat;0%nat]^^(S(S k)+1)).
  rewrite <-lpow_add. f_equal. lia.
Qed.

Lemma suffix_EA_C k:
  4%nat::5%nat::3%nat::
    ([1%nat;0%nat]^^S k++[1%nat;0%nat]^^3)=
  cells [LB] 3%nat++[3%nat;1%nat]++
    [0%nat;1%nat]^^(S(S k)+1)++[0%nat].
Proof.
  rewrite A_stream. cbn [cells total ltotal pair_cells Nat.add].
  repeat rewrite <-app_assoc. repeat rewrite <-lpow_add.
  cbn [app].
  do 3 f_equal.
  change ([1%nat;0%nat]^^(S k+3)=
    [1%nat;0%nat]^^1++[1%nat;0%nat]^^S(S(k+1))).
  rewrite <-lpow_add. f_equal. lia.
Qed.

Lemma suffix_EA_DE k:
  4%nat::4%nat::0%nat::
    ([1%nat;0%nat]^^S k++[1%nat;0%nat]^^1)=
  cells [LC] 0%nat++[0%nat;1%nat]^^S(S k)++[0%nat].
Proof.
  rewrite A_stream. cbn [cells total ltotal pair_cells Nat.add].
  repeat rewrite <-app_assoc. repeat rewrite <-lpow_add.
  cbn [app]. do 3 f_equal. f_equal. lia.
Qed.

Lemma suffix_ED_AB k:
  7%nat::5%nat::3%nat::
    ([1%nat;0%nat]^^S k++[1%nat;0%nat]^^4)=
  cells [LE;LD;LA] 0%nat++
    [0%nat;1%nat]^^(S k+2)++[0%nat].
Proof.
  rewrite A_stream. cbn [cells total ltotal pair_cells Nat.add].
  repeat rewrite <-app_assoc. repeat rewrite <-lpow_add.
  cbn [app].
  do 3 f_equal.
  change ([1%nat;0%nat]^^(S k+4)=
    [1%nat;0%nat]^^2++[1%nat;0%nat]^^(S k+2)).
  rewrite <-lpow_add. f_equal. lia.
Qed.

Lemma suffix_ED_C k:
  7%nat::5%nat::3%nat::
    ([1%nat;0%nat]^^S k++[1%nat;0%nat]^^3)=
  cells [LE] 3%nat++[3%nat;1%nat]++
    [0%nat;1%nat]^^(S k+2)++[0%nat].
Proof.
  rewrite A_stream. cbn [cells total ltotal pair_cells Nat.add].
  repeat rewrite <-app_assoc. repeat rewrite <-lpow_add.
  cbn [app].
  do 3 f_equal.
  change ([1%nat;0%nat]^^(S k+3)=
    [1%nat;0%nat]^^1++[1%nat;0%nat]^^(S k+2)).
  rewrite <-lpow_add. f_equal. lia.
Qed.

Lemma step_EA_A xs r:
  total(LA::xs)+phase LA=2*length(LA::xs) ->
  2<=r ->
  double_reset(map W1(numbers EA (LA::xs) r))=
  Some(map W1(numbers EA (xs++[LB;LD;LA]) (r+1))).
Proof.
  intros H Hr. destruct r as [|[|k]]; try lia.
  rewrite numbers_EA,A_stream_two.
  cbn [cells total ltotal phase pair_cells length] in H |- *.
  rewrite regroup_010.
  replace (total xs) with (S(length(cells xs 0%nat++[0%nat]))) by
    (rewrite length_app,cells_length; cbn [length]; lia).
  rewrite !Nat.add_0_r.
  transitivity
    (Some(map W1
      (map (fun n => n+4) ((cells xs 0%nat++[0%nat])++[1%nat])++
       3%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^4))).
  - change
      (double_reset(map W1
        ([S(length(cells xs 0%nat++[0%nat]));
           S(length(cells xs 0%nat++[0%nat]))+1]++
         (cells xs 0%nat++[0%nat])++[1%nat]++
         0%nat::[1%nat;0%nat]^^S k))=
       Some(map W1
        (map (fun n => n+4) ((cells xs 0%nat++[0%nat])++[1%nat])++
         3%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^4))).
    apply double_formula_last.
    + intro E. apply app_eq_nil in E as [_ E]. discriminate.
    + rewrite length_app,cells_length. cbn [length]. lia.
  - f_equal.
    rewrite numbers_EA,cells_app. cbn [total ltotal].
    replace (1+(3+(0+0))+0) with (0+4) by lia.
    rewrite (cells_add xs 0 4),!map_app.
    repeat rewrite <-app_assoc.
    repeat rewrite <-map_app.
    cbn [map app Nat.add].
    now rewrite suffix_EA_A.
Qed.

Lemma step_EA_B xs r:
  total(LB::xs)+phase LB=2*length(LB::xs) ->
  2<=r ->
  double_reset(map W1(numbers EA (LB::xs) r))=
  Some(map W1(numbers EA (xs++[LB;LD;LA]) (r+1))).
Proof.
  intros H Hr. destruct r as [|[|k]]; try lia.
  rewrite numbers_EA,A_stream_two.
  cbn [cells total ltotal phase pair_cells length] in H |- *.
  rewrite regroup_010.
  rewrite !Nat.add_0_r.
  set (a:=S(length(cells xs 0%nat++[0%nat]))).
  replace (total xs+1) with a by
    (unfold a; rewrite length_app,cells_length; cbn [length]; lia).
  replace (total xs+2) with (a+1) by
    (unfold a; rewrite length_app,cells_length; cbn [length]; lia).
  transitivity
    (Some(map W1
      (map (fun n => n+4) ((cells xs 0%nat++[0%nat])++[1%nat])++
       3%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^4))).
  - subst a. apply double_formula_last.
    + intro E. apply app_eq_nil in E as [_ E]. discriminate.
    + rewrite length_app,cells_length. cbn [length]. lia.
  - f_equal.
    rewrite numbers_EA,cells_app. cbn [total ltotal].
    replace (1+(3+(0+0))+0) with (0+4) by lia.
    rewrite (cells_add xs 0 4),!map_app.
    repeat rewrite <-app_assoc. repeat rewrite <-map_app.
    cbn [map app Nat.add]. now rewrite suffix_EA_A.
Qed.

Lemma step_EA_C xs r:
  total(LC::xs)+phase LC=2*length(LC::xs) ->
  2<=r ->
  double_reset(map W1(numbers EA (LC::xs) r))=
  Some(map W1(numbers ED (xs++[LB]) (r+1))).
Proof.
  intros H Hr. destruct r as [|[|k]]; try lia.
  rewrite numbers_EA,A_stream_two.
  cbn [cells total ltotal phase pair_cells length] in H |- *.
  rewrite regroup_010.
  rewrite !Nat.add_0_r.
  set (a:=S(length(cells xs 0%nat++[0%nat]))).
  replace (total xs+4) with a by
    (unfold a; rewrite length_app,cells_length; cbn [length]; lia).
  transitivity
    (Some(map W1
      (map (fun n => n+4) ((cells xs 0%nat++[0%nat])++[1%nat])++
       3%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^3))).
  - subst a. apply double_formula_last.
    + intro E. apply app_eq_nil in E as [_ E]. discriminate.
    + rewrite length_app,cells_length. cbn [length]. lia.
  - f_equal.
    rewrite numbers_ED,cells_app. cbn [total ltotal].
    replace (1+0+3) with (0+4) by lia.
    rewrite (cells_add xs 0 4),!map_app.
    repeat rewrite <-app_assoc. repeat rewrite <-map_app.
    cbn [map app Nat.add]. now rewrite suffix_EA_C.
Qed.

Lemma step_EA_D xs r:
  total(LD::xs)+phase LD=2*length(LD::xs) ->
  2<=r ->
  double_reset(map W1(numbers EA (LD::xs) r))=
  Some(map W1(numbers EA (xs++[LC]) r)).
Proof.
  intros H Hr. destruct xs as [|y ys].
  { cbn [total ltotal phase length] in H. lia. }
  destruct r as [|[|k]]; try lia.
  rewrite numbers_EA,A_stream.
  cbn [cells total ltotal phase pair_cells length] in H |- *.
  rewrite regroup_odd.
  rewrite !Nat.add_0_r.
  assert (Hp:pair_cells y (total ys)++cells ys 0%nat=
    cells(y::ys) 0%nat).
  { cbn [cells]. now rewrite Nat.add_0_r. }
  rewrite Hp.
  set (a:=S(length(cells (y::ys) 0%nat))).
  replace (ltotal y+total ys+3) with a by
    (unfold a; rewrite cells_length; cbn [total length]; lia).
  replace (ltotal y+total ys+1) with (a-2) by
    (unfold a; rewrite cells_length; cbn [total length]; lia).
  transitivity
    (Some(map W1
      (map (fun n => n+4) (cells(y::ys) 0%nat++[0%nat])++
       4%nat::0%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^1))).
  - subst a.
    apply (double_formula_last
      (S(length(cells(y::ys) 0%nat))-2) (cells(y::ys) 0%nat)
      0%nat 1%nat (0%nat::[1%nat;0%nat]^^S k) 0%nat).
    + destruct y; cbn [cells pair_cells]; discriminate.
    + rewrite cells_length. cbn [length]. lia.
  - f_equal.
    rewrite numbers_EA,cells_app. cbn [total ltotal].
    replace (4+0+0) with (0+4) by lia.
    rewrite (cells_add (y::ys) 0 4),!map_app.
    repeat rewrite <-app_assoc. repeat rewrite <-map_app.
    cbn [map app Nat.add]. now rewrite suffix_EA_DE.
Qed.

Lemma step_EA_E xs r:
  total(LE::xs)+phase LE=2*length(LE::xs) ->
  2<=r ->
  double_reset(map W1(numbers EA (LE::xs) r))=
  Some(map W1(numbers EA (xs++[LC]) r)).
Proof.
  intros H Hr. destruct xs as [|y ys].
  { cbn [total ltotal phase length] in H. lia. }
  destruct r as [|[|k]]; try lia.
  rewrite numbers_EA,A_stream.
  cbn [cells total ltotal phase pair_cells length] in H |- *.
  rewrite regroup_odd.
  rewrite !Nat.add_0_r.
  assert (Hp:pair_cells y (total ys)++cells ys 0%nat=
    cells(y::ys) 0%nat).
  { cbn [cells]. now rewrite Nat.add_0_r. }
  rewrite Hp.
  set (a:=S(length(cells (y::ys) 0%nat))).
  replace (ltotal y+total ys+4) with a by
    (unfold a; rewrite cells_length; cbn [total length]; lia).
  replace (ltotal y+total ys+2) with (a-2) by
    (unfold a; rewrite cells_length; cbn [total length]; lia).
  transitivity
    (Some(map W1
      (map (fun n => n+4) (cells(y::ys) 0%nat++[0%nat])++
       4%nat::0%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^1))).
  - subst a.
    apply (double_formula_last
      (S(length(cells(y::ys) 0%nat))-2) (cells(y::ys) 0%nat)
      0%nat 1%nat (0%nat::[1%nat;0%nat]^^S k) 0%nat).
    + destruct y; cbn [cells pair_cells]; discriminate.
    + rewrite cells_length. cbn [length]. lia.
  - f_equal.
    rewrite numbers_EA,cells_app. cbn [total ltotal].
    replace (4+0+0) with (0+4) by lia.
    rewrite (cells_add (y::ys) 0 4),!map_app.
    repeat rewrite <-app_assoc. repeat rewrite <-map_app.
    cbn [map app Nat.add]. now rewrite suffix_EA_DE.
Qed.

Lemma step_ED_A xs r:
  total(LA::xs)+3+phase LA=2*length(LA::xs) ->
  1<=r ->
  double_reset(map W1(numbers ED (LA::xs) r))=
  Some(map W1(numbers EA (xs++[LE;LD;LA]) (r+2))).
Proof.
  intros H Hr. destruct r as [|k]; try lia.
  rewrite numbers_ED,A_stream.
  cbn [cells total ltotal phase pair_cells length] in H |- *.
  rewrite regroup_c10'.
  set (a:=S(length(cells xs 3%nat++[3%nat]))).
  replace (total xs+3) with a by
    (unfold a; rewrite length_app,cells_length; cbn [length]; lia).
  replace (total xs+4) with (a+1) by
    (unfold a; rewrite length_app,cells_length; cbn [length]; lia).
  transitivity
    (Some(map W1
      (map (fun n => n+4) ((cells xs 3%nat++[3%nat])++[1%nat])++
       3%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^4))).
  - subst a. apply double_formula_last.
    + intro E. apply app_eq_nil in E as [_ E]. discriminate.
    + rewrite length_app,cells_length. cbn [length]. lia.
  - f_equal.
    rewrite numbers_EA,cells_app. cbn [total ltotal].
    replace (4+(3+(0+0))+0) with (3+4) by lia.
    rewrite (cells_add xs 3 4),!map_app.
    repeat rewrite <-app_assoc. repeat rewrite <-map_app.
    cbn [map app Nat.add]. now rewrite suffix_ED_AB.
Qed.

Lemma step_ED_B xs r:
  total(LB::xs)+3+phase LB=2*length(LB::xs) ->
  1<=r ->
  double_reset(map W1(numbers ED (LB::xs) r))=
  Some(map W1(numbers EA (xs++[LE;LD;LA]) (r+2))).
Proof.
  intros H Hr. destruct r as [|k]; try lia.
  rewrite numbers_ED,A_stream.
  cbn [cells total ltotal phase pair_cells length] in H |- *.
  rewrite regroup_c10'.
  set (a:=S(length(cells xs 3%nat++[3%nat]))).
  replace (total xs+3+1) with a by
    (unfold a; rewrite length_app,cells_length; cbn [length]; lia).
  replace (total xs+3+2) with (a+1) by
    (unfold a; rewrite length_app,cells_length; cbn [length]; lia).
  transitivity
    (Some(map W1
      (map (fun n => n+4) ((cells xs 3%nat++[3%nat])++[1%nat])++
       3%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^4))).
  - subst a. apply double_formula_last.
    + intro E. apply app_eq_nil in E as [_ E]. discriminate.
    + rewrite length_app,cells_length. cbn [length]. lia.
  - f_equal.
    rewrite numbers_EA,cells_app. cbn [total ltotal].
    replace (4+(3+(0+0))+0) with (3+4) by lia.
    rewrite (cells_add xs 3 4),!map_app.
    repeat rewrite <-app_assoc. repeat rewrite <-map_app.
    cbn [map app Nat.add]. now rewrite suffix_ED_AB.
Qed.

Lemma step_ED_C xs r:
  total(LC::xs)+3+phase LC=2*length(LC::xs) ->
  1<=r ->
  double_reset(map W1(numbers ED (LC::xs) r))=
  Some(map W1(numbers ED (xs++[LE]) (r+2))).
Proof.
  intros H Hr. destruct r as [|k]; try lia.
  rewrite numbers_ED,A_stream.
  cbn [cells total ltotal phase pair_cells length] in H |- *.
  rewrite regroup_c10'.
  set (a:=S(length(cells xs 3%nat++[3%nat]))).
  replace (total xs+3+4) with a by
    (unfold a; rewrite length_app,cells_length; cbn [length]; lia).
  transitivity
    (Some(map W1
      (map (fun n => n+4) ((cells xs 3%nat++[3%nat])++[1%nat])++
       3%nat::[1%nat;0%nat]^^S k++[1%nat;0%nat]^^3))).
  - subst a. apply double_formula_last.
    + intro E. apply app_eq_nil in E as [_ E]. discriminate.
    + rewrite length_app,cells_length. cbn [length]. lia.
  - f_equal.
    rewrite numbers_ED,cells_app. cbn [total ltotal].
    replace (4+0+3) with (3+4) by lia.
    rewrite (cells_add xs 3 4),!map_app.
    repeat rewrite <-app_assoc. repeat rewrite <-map_app.
    cbn [map app Nat.add]. now rewrite suffix_ED_C.
Qed.

Definition follows x y:Prop :=
  match x,y with
  | LA,LA | LA,LB | LA,LC
  | LB,LD | LB,LE
  | LC,LA | LC,LB | LC,LC
  | LD,LA
  | LE,LD | LE,LE => True
  | _,_ => False
  end.

Inductive Chain:list letter->Prop :=
| Chain_one x: Chain[x]
| Chain_cons x y xs: follows x y -> Chain(y::xs) -> Chain(x::y::xs).

Definition end_ok e x:Prop :=
  match e,x with
  | EA,LA | EA,LC | ED,LB | ED,LE => True
  | _,_ => False
  end.

Definition head_ok e x:Prop :=
  match e,x with ED,LD | ED,LE => False | _,_ => True end.

Definition enough e r:Prop := match e with EA => 2<=r | ED => 1<=r end.

Record Good (p:edge*list letter*nat):Prop := {
  good_chain: Chain (let '(_,left,_):=p in left);
  good_end: end_ok (let '(e,_,_):=p in e)
    (last (let '(_,left,_):=p in left) LA);
  good_head: head_ok (let '(e,_,_):=p in e)
    (hd LA (let '(_,left,_):=p in left));
  good_enough: enough (let '(e,_,_):=p in e)
    (let '(_,_,r):=p in r);
  good_sum:
    total (let '(_,left,_):=p in left)+
    edge_total (let '(e,_,_):=p in e)+
    phase (hd LA (let '(_,left,_):=p in left))=
    2*length(let '(_,left,_):=p in left)
}.

Definition advance (p:edge*list letter*nat):option(edge*list letter*nat) :=
  match p with
  | (EA,LA::xs,r) | (EA,LB::xs,r) =>
      Some(EA,xs++[LB;LD;LA],r+1)
  | (EA,LC::xs,r) => Some(ED,xs++[LB],r+1)
  | (EA,LD::xs,r) | (EA,LE::xs,r) => Some(EA,xs++[LC],r)
  | (ED,LA::xs,r) | (ED,LB::xs,r) =>
      Some(EA,xs++[LE;LD;LA],r+2)
  | (ED,LC::xs,r) => Some(ED,xs++[LE],r+2)
  | _ => None
  end.

Lemma Chain_snoc xs x:
  Chain xs -> follows(last xs LA) x -> Chain(xs++[x]).
Proof.
  intros H. induction H.
  - cbn. intros Hxy. constructor; [exact Hxy|constructor].
  - cbn. intros Hlast. constructor; auto.
Qed.

Lemma last_app_cons {A}(xs:list A) y ys d:
  last(xs++y::ys) d=last(y::ys) d.
Proof. induction xs; cbn; auto. destruct xs; cbn in *; auto. Qed.

Lemma end_EA_B x: end_ok EA x -> follows x LB.
Proof. destruct x; cbn; auto. Qed.

Lemma end_EA_C x: end_ok EA x -> follows x LC.
Proof. destruct x; cbn; auto. Qed.

Lemma end_ED_E x: end_ok ED x -> follows x LE.
Proof. destruct x; cbn; auto. Qed.

Lemma tail_append_BDA f xs:
  Chain(f::xs) -> end_ok EA (last(f::xs) LA) ->
  Chain(xs++[LB;LD;LA]).
Proof.
  intros Hc He. destruct xs as [|x xs].
  - repeat constructor; cbn; exact I.
  - inverts Hc. cbn in He.
    replace ((x::xs)++[LB;LD;LA]) with
      ((((x::xs)++[LB])++[LD])++[LA]) by
      (repeat rewrite <-app_assoc; reflexivity).
    apply Chain_snoc; [apply Chain_snoc; [apply Chain_snoc|]|].
    + exact H3.
    + apply end_EA_B,He.
    + rewrite last_app_cons. exact I.
    + rewrite last_app_cons. exact I.
Qed.

Lemma tail_append_B f xs:
  Chain(f::xs) -> end_ok EA (last(f::xs) LA) ->
  Chain(xs++[LB]).
Proof.
  intros Hc He. destruct xs as [|x xs].
  - constructor.
  - inverts Hc. cbn in He. apply Chain_snoc; [exact H3|apply end_EA_B,He].
Qed.

Lemma tail_append_C f xs:
  Chain(f::xs) -> end_ok EA (last(f::xs) LA) ->
  Chain(xs++[LC]).
Proof.
  intros Hc He. destruct xs as [|x xs].
  - constructor.
  - inverts Hc. cbn in He. apply Chain_snoc; [exact H3|apply end_EA_C,He].
Qed.

Lemma tail_append_EDA f xs:
  Chain(f::xs) -> end_ok ED (last(f::xs) LA) ->
  Chain(xs++[LE;LD;LA]).
Proof.
  intros Hc He. destruct xs as [|x xs].
  - repeat constructor; cbn; exact I.
  - inverts Hc. cbn in He.
    replace ((x::xs)++[LE;LD;LA]) with
      ((((x::xs)++[LE])++[LD])++[LA]) by
      (repeat rewrite <-app_assoc; reflexivity).
    apply Chain_snoc; [apply Chain_snoc; [apply Chain_snoc|]|].
    + exact H3.
    + apply end_ED_E,He.
    + rewrite last_app_cons. exact I.
    + rewrite last_app_cons. exact I.
Qed.

Lemma tail_append_E f xs:
  Chain(f::xs) -> end_ok ED (last(f::xs) LA) ->
  Chain(xs++[LE]).
Proof.
  intros Hc He. destruct xs as [|x xs].
  - constructor.
  - inverts Hc. cbn in He. apply Chain_snoc; [exact H3|apply end_ED_E,He].
Qed.

Ltac finish_good_sum Hc xs :=
  rewrite total_app;
  destruct xs as [|y ys];
  [cbn [total ltotal edge_total phase length app hd] in *; lia|
   inverts Hc; destruct y;
   rewrite length_app;
   cbn [follows total ltotal edge_total phase length app hd] in *;
   try contradiction; lia].

Ltac finish_ED_head Hc xs :=
  destruct xs as [|y ys];
  [cbn [total ltotal edge_total phase length app hd] in *; lia|
   inverts Hc; destruct y;
   cbn [follows head_ok] in *; try contradiction; exact I].

Lemma Good_step p:
  Good p -> exists p', advance p=Some p' /\ Good p'.
Proof.
  destruct p as [[e left] r]. destruct left as [|f xs].
  { intros G. destruct G as [Hc]. inverts Hc. }
  intros G. destruct G as [Hc He Hh Hr Hs].
  cbn in Hc,He,Hh,Hr,Hs. destruct e,f.
  - exists(EA,xs++[LB;LD;LA],r+1). split; [reflexivity|].
    constructor.
    + apply tail_append_BDA with (f:=LA); assumption.
    + rewrite last_app_cons. exact I.
    + exact I.
    + cbn [enough] in *. lia.
    + rewrite total_app. destruct xs as [|y ys].
      * cbn [total ltotal edge_total phase length] in *.
        cbn [app hd] in *. lia.
      * inverts Hc. destruct y;
        rewrite length_app;
        cbn [follows total ltotal edge_total phase length app hd] in *;
        try contradiction; lia.
  - exists(EA,xs++[LB;LD;LA],r+1). split; [reflexivity|].
    constructor.
    + apply tail_append_BDA with (f:=LB); assumption.
    + rewrite last_app_cons. exact I.
    + exact I.
    + cbn [enough] in *. lia.
    + finish_good_sum Hc xs.
  - exists(ED,xs++[LB],r+1). split; [reflexivity|].
    constructor.
    + apply tail_append_B with (f:=LC); assumption.
    + rewrite last_app_cons. exact I.
    + finish_ED_head Hc xs.
    + cbn [enough] in *. lia.
    + finish_good_sum Hc xs.
  - exists(EA,xs++[LC],r). split; [reflexivity|].
    constructor.
    + apply tail_append_C with (f:=LD); assumption.
    + rewrite last_app_cons. exact I.
    + exact I.
    + exact Hr.
    + finish_good_sum Hc xs.
  - exists(EA,xs++[LC],r). split; [reflexivity|].
    constructor.
    + apply tail_append_C with (f:=LE); assumption.
    + rewrite last_app_cons. exact I.
    + exact I.
    + exact Hr.
    + finish_good_sum Hc xs.
  - exists(EA,xs++[LE;LD;LA],r+2). split; [reflexivity|].
    constructor.
    + apply tail_append_EDA with (f:=LA); assumption.
    + rewrite last_app_cons. exact I.
    + exact I.
    + cbn [enough] in *. lia.
    + finish_good_sum Hc xs.
  - exists(EA,xs++[LE;LD;LA],r+2). split; [reflexivity|].
    constructor.
    + apply tail_append_EDA with (f:=LB); assumption.
    + rewrite last_app_cons. exact I.
    + exact I.
    + cbn [enough] in *. lia.
    + finish_good_sum Hc xs.
  - exists(ED,xs++[LE],r+2). split; [reflexivity|].
    constructor.
    + apply tail_append_E with (f:=LC); assumption.
    + rewrite last_app_cons. exact I.
    + finish_ED_head Hc xs.
    + cbn [enough] in *. lia.
    + finish_good_sum Hc xs.
  - cbn [head_ok] in Hh. contradiction.
  - cbn [head_ok] in Hh. contradiction.
Qed.

Lemma advance_sound p p':
  Good p -> advance p=Some p' ->
  double_reset
    (map W1(numbers (let '(e,_,_):=p in e)
      (let '(_,left,_):=p in left) (let '(_,_,r):=p in r)))=
  Some(map W1(numbers (let '(e,_,_):=p' in e)
    (let '(_,left,_):=p' in left) (let '(_,_,r):=p' in r))).
Proof.
  destruct p as [[e left] r]. destruct left as [|f xs].
  { intros G. destruct G as [Hc]. inverts Hc. }
  intros G Ha. destruct G as [Hc He Hh Hr Hs].
  cbn [total ltotal edge_total phase hd length enough]
    in Hc,He,Hh,Hr,Hs.
  destruct e,f;
    cbn [total ltotal edge_total phase length enough] in Hs,Hr;
    cbn in Ha; try discriminate;
    inverts Ha; cbn.
  - apply step_EA_A.
    + cbn [total ltotal phase length]. lia.
    + exact Hr.
  - apply step_EA_B; [cbn [total ltotal phase length]; lia|exact Hr].
  - apply step_EA_C; [cbn [total ltotal phase length]; lia|exact Hr].
  - apply step_EA_D; [cbn [total ltotal phase length]; lia|exact Hr].
  - apply step_EA_E; [cbn [total ltotal phase length]; lia|exact Hr].
  - apply step_ED_A; [cbn [total ltotal phase length]; lia|exact Hr].
  - apply step_ED_B; [cbn [total ltotal phase length]; lia|exact Hr].
  - apply step_ED_C; [cbn [total ltotal phase length]; lia|exact Hr].
Qed.

Definition entry:=(EA,[LC;LB;LD;LA],2%nat).

Lemma seed: Good entry.
Proof.
  constructor.
  - repeat constructor; exact I.
  - reflexivity.
  - exact I.
  - cbn [entry enough]. lia.
  - reflexivity.
Qed.

Lemma init_side:
  words_side(map W1
    [3%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat])=
  D1 3 *> (D1 1++D1 0)^^3 *> 0inf.
Proof. reflexivity. Qed.

Lemma init_entry: c0 -->* State entry.
Proof.
  eapply evstep_trans; [exact init|].
  rewrite <-init_side.
  eapply evstep_trans with (c':=S'(O,words_side(map W1
    [4%nat;5%nat;4%nat;4%nat;0%nat;1%nat;0%nat]))).
  - apply progress_evstep,double_reset_sound. reflexivity.
  - apply progress_evstep,double_reset_sound. reflexivity.
Qed.

Lemma Good_progress p:
  Good p -> exists p', State p -->+ State p' /\ Good p'.
Proof.
  intros G. destruct (Good_step _ G) as [p'[Ha G']].
  exists p'. split; [|exact G'].
  destruct p as [[e left] r]. destruct p' as [[e' left'] r']. cbn in *.
  unfold State. apply double_reset_sound. exact (advance_sound _ _ G Ha).
Qed.

Lemma macro_nonhalt: ~halts tm (State entry).
Proof.
  eapply (progress_nonhalt_cond tm (edge*list letter*nat)
    entry State Good).
  - exact Good_progress.
  - exact seed.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply multistep_nonhalt; [exact init_entry|exact macro_nonhalt]. Qed.

Print Assumptions nonhalt.

End TM1.
