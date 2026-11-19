From BusyCoq Require Import Individual62 InfiniteRect LongN.
Require Import Bool.
Require Import List.
Require Import Lia.
Require Import PeanoNat.
Require Import String.
Require Import ZifyNat.

Open Scope list.
Close Scope sym_scope.

Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0RA_0LC0LB_1RD0LF_1RD0RE_1LA1RE_---1LE").

Inductive Tok :=
| RTok (q : Q)
| LTok (q : Q).

Definition tok_eqb a b :=
  match a,b with
  | RTok q1, RTok q2 => q_eqb q1 q2
  | LTok q1, LTok q2 => q_eqb q1 q2
  | _, _ => false
  end.

Record Boundary := {
  b_mu : nat;
  b_p : nat;
  b_pre : list Tok;
  b_per : list Tok;
}.

Definition tok_default := RTok A.

Definition tok_at (b : Boundary) n :=
  if n <? b.(b_mu) then
    nth n b.(b_pre) tok_default
  else
    nth ((n - b.(b_mu)) mod b.(b_p)) b.(b_per) tok_default.

Fixpoint write_sym n s xs :=
  match n,xs with
  | O, [] => [s]
  | O, _::xs => s::xs
  | S n, [] => S0::write_sym n s []
  | S n, x::xs => x::write_sym n s xs
  end.

Record RunState := {
  rs_left : nat;
  rs_q : Q;
  rs_pos : nat;
  rs_tape : list Sym;
  rs_out : list Tok;
}.

Definition finish_or_continue need (st : RunState) tok :=
  let out := tok :: st.(rs_out) in
  if need <=? List.length out then
    Some (inr (rev out))
  else
    Some (inl {|
      rs_left := st.(rs_left);
      rs_q := st.(rs_q);
      rs_pos := st.(rs_pos);
      rs_tape := st.(rs_tape);
      rs_out := out;
    |}).

Definition run_step (b : Boundary) need (st : RunState) :=
  let s := nth st.(rs_pos) st.(rs_tape) S0 in
  match tm (st.(rs_q), s) with
  | None => None
  | Some (s', d, q') =>
      let tape' := write_sym st.(rs_pos) s' st.(rs_tape) in
      match d with
      | R =>
          let st' := {|
            rs_left := st.(rs_left);
            rs_q := q';
            rs_pos := S st.(rs_pos);
            rs_tape := tape';
            rs_out := st.(rs_out);
          |} in
          match st.(rs_pos) with
          | O => finish_or_continue need st' (RTok q')
          | S _ => Some (inl st')
          end
      | L =>
          match st.(rs_pos) with
          | O =>
              if tok_eqb (LTok q') (tok_at b st.(rs_left)) then
                match tok_at b (S st.(rs_left)) with
                | RTok qin =>
                    Some (inl {|
                      rs_left := st.(rs_left) + 2;
                      rs_q := qin;
                      rs_pos := O;
                      rs_tape := tape';
                      rs_out := st.(rs_out);
                    |})
                | LTok _ => None
                end
              else None
          | S pos' =>
              let st' := {|
                rs_left := st.(rs_left);
                rs_q := q';
                rs_pos := pos';
                rs_tape := tape';
                rs_out := st.(rs_out);
              |} in
              match pos' with
              | O => finish_or_continue need st' (LTok q')
              | S _ => Some (inl st')
              end
          end
      end
  end.

Fixpoint run_until fuel (b : Boundary) need (st : RunState) :=
  if need <=? List.length st.(rs_out) then Some (rev st.(rs_out)) else
  match fuel with
  | O => None
  | S fuel =>
      match run_step b need st with
      | Some (inl st') => run_until fuel b need st'
      | Some (inr out) => Some out
      | None => None
      end
  end.

Definition initial_state (b : Boundary) :=
  match tok_at b O with
  | RTok q => Some {|
      rs_left := 1;
      rs_q := q;
      rs_pos := O;
      rs_tape := [];
      rs_out := [];
    |}
  | LTok _ => None
  end.

Definition gen_fuel need := 1000 + 50 * (need + 10).

Definition empty_boundary mu p := {|
  b_mu := mu;
  b_p := p;
  b_pre := [];
  b_per := [];
|}.

Definition gen_next (b : Boundary) mu p :=
  let need := mu + p in
  match initial_state b with
  | Some st =>
      match run_until (gen_fuel need) b need st with
      | Some out => {|
          b_mu := mu;
          b_p := p;
          b_pre := firstn mu out;
          b_per := firstn p (skipn mu out);
        |}
      | None => empty_boundary mu p
      end
  | None => empty_boundary mu p
  end.

Definition B0_pre :=
  [RTok E; LTok A; RTok E; LTok B; RTok E; LTok A; RTok E; LTok B;
   RTok E; LTok A; RTok E; LTok B; RTok E; LTok A; RTok E; LTok E].

Definition B0_per :=
  [RTok A; LTok C; RTok D; LTok B; RTok E; LTok A].

Definition B0 := {|
  b_mu := 16;
  b_p := 6;
  b_pre := B0_pre;
  b_per := B0_per;
|}.

Definition len_table : list (nat*nat) :=
  [(16,6); (24,18); (18,22); (18,20); (14,26); (22,18); (18,4); (14,6);
   (10,18); (10,22); (6792,20); (8834,26); (6122,18); (4172,4); (6248,6); (4678,18);
   (5722,22); (5206,20); (6724,26); (4660,18); (3226,4); (4794,6); (3606,18); (4378,22);
   (3966,20); (5124,26); (3552,18); (2408,4); (3540,6); (2674,18); (3240,22); (2948,20);
   (3744,26); (2630,18); (1866,4); (2616,6); (2024,18); (2348,22); (2434,20); (3130,26);
   (2200,18); (1576,4); (2178,6); (1678,18); (2024,22); (1880,20); (2354,26); (1684,18);
   (1228,4); (1714,6); (1344,18); (1516,22); (1386,20); (1712,26); (1242,18); (944,4);
   (1212,6); (932,18); (1080,22); (974,20); (1176,26); (868,18); (688,4); (860,6);
   (698,18); (758,22); (1034,20); (1270,26); (920,18); (710,4); (910,6); (756,18);
   (844,22); (750,20); (888,26); (670,18); (550,4); (676,6); (554,18); (600,22);
   (522,20); (628,26); (450,18); (382,4); (448,6); (376,18); (414,22); (482,20);
   (574,26); (416,18); (346,4); (404,6); (324,18); (338,22); (286,20); (332,26);
   (262,18); (264,4); (270,6); (226,18); (222,22); (200,20); (252,26); (202,18);
   (176,4); (162,6); (148,18); (140,22); (124,20); (114,26); (84,18); (98,4);
   (84,6); (82,18); (82,22); (80,20); (70,26); (62,18); (62,4); (74,6);
   (62,18); (70,22); (62,20); (48,26); (52,18); (46,4); (52,6); (50,18);
   (48,22); (40,20); (32,26); (28,18); (40,4); (42,6); (32,18); (38,22);
   (24,20); (16,26); (20,18); (14,4); (18,6); (22,18); (20,22); (20,20);
   (14,26); (18,18); (12,4); (10,6); (10,18); (6,22); (2,20); (O,26);
   (O,18); (16,4); (24,6); (18,18); (20,22); (12,20); (8,26); (8,18);
   (10,4)].

Definition len_at i := nth i len_table (O,2).

Fixpoint build_boundaries_from i n b :=
  match n with
  | O => [b]
  | S n =>
      let '(mu,p) := len_at (S i) in
      let b' := gen_next b mu p in
      b :: build_boundaries_from (S i) n b'
  end.

Definition boundaries := build_boundaries_from O 160 B0.

Definition boundary i := nth i boundaries B0.

Lemma boundary0:
  boundary O = B0.
Proof.
  reflexivity.
Qed.

Definition pair_default : DH0*DH0 := ((A,[]),(A,[])).

Definition pair_of_tokens a b :=
  match a,b with
  | RTok qR, LTok qL => ((qR,[]),(qL,[]))
  | _, _ => pair_default
  end.

Definition pair_at b k :=
  pair_of_tokens (tok_at b (k*2)) (tok_at b (S (k*2))).

Fixpoint pair_list b off len :=
  match len with
  | O => []
  | S len => pair_at b off :: pair_list b (S off) len
  end.

CoFixpoint pair_stream_from b off : Stream (DH0*DH0) :=
  Cons (pair_at b off) (pair_stream_from b (S off)).

Definition pair_pre_len b := (b.(b_mu) + 1) / 2.
Definition pair_per_len b := b.(b_p) / 2.

Definition row_table : list (nat*nat*nat*nat*nat*nat) :=
  [(1,16,24,21,24,18); (2,24,18,20,18,22); (3,18,20,21,22,20);
   (4,18,14,23,20,26); (5,16,22,22,26,18); (6,22,20,15,18,12);
   (7,18,14,5,4,6); (8,14,10,21,24,18); (9,10,10,20,18,22);
   (10,7466,6792,21,22,20); (11,6792,8836,23,20,26); (12,8834,6122,22,26,18);
   (13,6254,4174,15,18,12); (14,4172,6248,5,4,6); (15,6248,4678,21,24,18);
   (16,4678,5722,20,18,22); (17,5722,5208,21,22,20); (18,5206,6726,23,20,26);
   (19,6724,4660,22,26,18); (20,4792,3228,15,18,12); (21,3226,4794,5,4,6);
   (22,4794,3606,21,24,18); (23,3606,4378,20,18,22); (24,4378,3968,21,22,20);
   (25,3966,5126,23,20,26); (26,5124,3552,22,26,18); (27,3552,2408,15,18,12);
   (28,2408,3540,5,4,6); (29,3540,2676,21,24,18); (30,2674,3242,20,18,22);
   (31,3240,2948,21,22,20); (32,2948,3744,23,20,26); (33,3744,2630,22,26,18);
   (34,2630,1866,15,18,12); (35,1868,2616,5,4,6); (36,2616,2024,21,24,18);
   (37,2024,2348,20,18,22); (38,2718,2434,21,22,20); (39,2434,3132,23,20,26);
   (40,3130,2200,22,26,18); (41,2200,1576,15,18,12); (42,1576,2178,5,4,6);
   (43,2178,1680,21,24,18); (44,1678,2026,20,18,22); (45,2104,1880,21,22,20);
   (46,1880,2356,23,20,26); (47,2354,1684,22,26,18); (48,1684,1228,15,18,12);
   (49,1228,1714,5,4,6); (50,1714,1346,21,24,18); (51,1344,1518,20,18,22);
   (52,1528,1386,21,22,20); (53,1386,1714,23,20,26); (54,1712,1242,22,26,18);
   (55,1242,944,15,18,12); (56,944,1212,5,4,6); (57,1212,934,21,24,18);
   (58,932,1082,20,18,22); (59,1080,974,21,22,20); (60,974,1176,23,20,26);
   (61,1176,868,22,26,18); (62,868,688,15,18,12); (63,690,860,5,4,6);
   (64,860,700,21,24,18); (65,698,760,20,18,22); (66,1146,1034,21,22,20);
   (67,1034,1272,23,20,26); (68,1270,920,22,26,18); (69,920,710,15,18,12);
   (70,710,910,5,4,6); (71,910,758,21,24,18); (72,756,846,20,18,22);
   (73,844,750,21,22,20); (74,750,888,23,20,26); (75,888,670,22,26,18);
   (76,670,550,15,18,12); (77,552,676,5,4,6); (78,676,554,21,24,18);
   (79,554,600,20,18,22); (80,600,524,21,22,20); (81,522,628,23,20,26);
   (82,628,450,22,26,18); (83,454,384,15,18,12); (84,382,448,5,4,6);
   (85,448,376,21,24,18); (86,376,414,20,18,22); (87,544,482,21,22,20);
   (88,482,576,23,20,26); (89,574,416,22,26,18); (90,416,346,15,18,12);
   (91,346,404,5,4,6); (92,404,326,21,24,18); (93,324,340,20,18,22);
   (94,338,286,21,22,20); (95,286,332,23,20,26); (96,332,262,22,26,18);
   (97,262,264,15,18,12); (98,266,270,5,4,6); (99,270,226,21,24,18);
   (100,226,222,20,18,22); (101,242,200,21,22,20); (102,200,254,23,20,26);
   (103,252,202,22,26,18); (104,202,176,15,18,12); (105,176,162,5,4,6);
   (106,162,150,21,24,18); (107,148,142,20,18,22); (108,140,124,21,22,20);
   (109,124,114,23,20,26); (110,114,84,22,26,18); (111,84,98,15,18,12);
   (112,100,84,5,4,6); (113,84,84,21,24,18); (114,82,84,20,18,22);
   (115,82,80,21,22,20); (116,80,70,23,20,26); (117,70,64,22,26,18);
   (118,62,62,15,18,12); (119,64,74,5,4,6); (120,74,64,21,24,18);
   (121,62,72,20,18,22); (122,70,62,21,22,20); (123,62,48,23,20,26);
   (124,48,54,22,26,18); (125,52,46,15,18,12); (126,48,52,5,4,6);
   (127,52,52,21,24,18); (128,50,50,20,18,22); (129,48,40,21,22,20);
   (130,40,32,23,20,26); (131,32,30,22,26,18); (132,46,42,15,18,12);
   (133,40,42,5,4,6); (134,42,32,21,24,18); (135,32,38,20,18,22);
   (136,38,26,21,22,20); (137,24,18,23,20,26); (138,16,20,22,26,18);
   (139,20,14,15,18,12); (140,14,18,5,4,6); (141,28,22,21,24,18);
   (142,22,22,20,18,22); (143,20,20,21,22,20); (144,20,14,23,20,26);
   (145,14,18,22,26,18); (146,18,12,15,18,12); (147,12,10,5,4,6);
   (148,10,10,21,24,18); (149,10,6,20,18,22); (150,6,4,21,22,20);
   (151,2,O,23,20,26); (152,O,O,22,26,18); (153,22,18,15,18,12);
   (154,16,24,5,4,6); (155,24,18,21,24,18); (156,18,20,20,18,22);
   (157,20,14,21,22,20); (158,12,10,23,20,26); (159,8,8,22,26,18);
   (160,14,12,15,18,12); (147,10,10,5,4,6)].

Definition row_at i := nth i row_table (S i,O,O,O,O,O).

Definition seg_bound := 10000.

Definition row_cert_at i addL addR w :=
  let '(j,l0,r0,_vis,dL,dR) := row_at i in
  let bL := boundary i in
  let bR := boundary j in
  let offL := l0 / 2 + addL in
  let offR := r0 / 2 + addR in
  let lenL := dL / 2 in
  let lenR := dR / 2 in
  andb (pair_pre_len bL <=? offL)
  (andb (pair_pre_len bR <=? offR)
  (andb (0 <? lenL)
  (andb (0 <? lenR)
  (andb (0 <? pair_per_len bL)
  (andb (0 <? pair_per_len bR)
  (andb (bL.(b_p) mod 2 =? 0)
  (andb (bR.(b_p) mod 2 =? 0)
  (andb (lenL mod pair_per_len bL =? 0)
  (andb (lenR mod pair_per_len bR =? 0)
  (andb
    (segRLs_n1_c tm (pair_list bL O offL) (pair_list bR O offR) [S0] w seg_bound)
    (segRLs_n1_c tm (pair_list bL offL lenL) (pair_list bR offR lenR) w w seg_bound))))))))))).

Definition row_choices : list (nat*nat*list Sym) :=
  [(0,0,[S0]); (0,0,[S1]); (0,1,[S0]); (0,1,[S1]);
   (1,0,[S0]); (1,0,[S1]); (1,1,[S0]); (1,1,[S1])].

Fixpoint find_row_choice i choices :=
  match choices with
  | [] => None
  | (addL,addR,w)::choices =>
      if row_cert_at i addL addR w then Some (addL,addR,w)
      else find_row_choice i choices
  end.

Definition row_choice i := find_row_choice i row_choices.

Definition row_cert i :=
  match row_choice i with
  | Some _ => true
  | None => false
  end.

Definition rows_ok := forallb row_cert (seq 0 161).

Lemma rows_ok_true:
  rows_ok = true.
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma forallb_in {A} (f : A -> bool) x xs:
  forallb f xs = true ->
  In x xs ->
  f x = true.
Proof.
  induction xs as [|y ys IH]; cbn.
  - contradiction.
  - intros H Hin.
    apply andb_true_iff in H as [Hy Hys].
    destruct Hin as [Heq|Hin].
    + subst.
      exact Hy.
    + eapply IH; eauto.
Qed.

Lemma find_row_choice_spec i choices addL addR w:
  find_row_choice i choices = Some (addL,addR,w) ->
  row_cert_at i addL addR w = true.
Proof.
  induction choices as [|[[addL0 addR0] w0] choices IH]; cbn.
  - congruence.
  - destruct (row_cert_at i addL0 addR0 w0) eqn:Hcert.
    + intro H.
      inversion H; subst.
      exact Hcert.
    + apply IH.
Qed.

Lemma row_choice_spec i addL addR w:
  row_choice i = Some (addL,addR,w) ->
  row_cert_at i addL addR w = true.
Proof.
  apply find_row_choice_spec.
Qed.

Opaque row_choice.

Definition row_target i := let '(j,_,_,_,_,_) := row_at i in j.
Definition row_L0 i := let '(_,l0,_,_,_,_) := row_at i in l0.
Definition row_R0 i := let '(_,_,r0,_,_,_) := row_at i in r0.
Definition row_dL i := let '(_,_,_,_,dL,_) := row_at i in dL.
Definition row_dR i := let '(_,_,_,_,_,dR) := row_at i in dR.

Definition src_off i add := row_L0 i / 2 + add.
Definition tgt_off i add := row_R0 i / 2 + add.
Definition src_len i := row_dL i / 2.
Definition tgt_len i := row_dR i / 2.

Definition src_prefix i add := pair_list (boundary i) O (src_off i add).
Definition tgt_prefix i add := pair_list (boundary (row_target i)) O (tgt_off i add).
Definition src_loop i add := pair_list (boundary i) (src_off i add) (src_len i).
Definition tgt_loop i add := pair_list (boundary (row_target i)) (tgt_off i add) (tgt_len i).

Definition true_boundary_stream i := pair_stream_from (boundary i) O.

Lemma pair_list_length b off len:
  List.length (pair_list b off len) = len.
Proof.
  revert off.
  induction len; intros off; cbn.
  - reflexivity.
  - rewrite IHlen.
    reflexivity.
Qed.

Lemma pair_stream_split b off len:
  pair_stream_from b off =
  pair_list b off len *> pair_stream_from b (off + len).
Proof.
  revert off.
  induction len; intros off; cbn.
  - replace (off + 0) with off by lia.
    reflexivity.
  - rewrite Cons_unfold at 1.
    cbn.
    rewrite IHlen.
    replace (S off + len) with (off + S len) by lia.
    reflexivity.
Qed.

Lemma pair_pre_len_bound b k:
  pair_pre_len b <= k ->
  b.(b_mu) <= k*2.
Proof.
  unfold pair_pre_len.
  lia.
Qed.

Lemma pair_period_double b:
  b.(b_p) mod 2 = 0 ->
  b.(b_p) = pair_per_len b * 2.
Proof.
  unfold pair_per_len.
  intro Hmod.
  pose proof (Nat.div_mod b.(b_p) 2 ltac:(lia)) as Hdiv.
  lia.
Qed.

Lemma period_shift_mod p per len k:
  p = per*2 ->
  per <> O ->
  len mod per = O ->
  ((k*len)*2) mod p = O.
Proof.
  intros Hp Hper Hmod.
  subst p.
  apply Nat.mod_divide; [lia|].
  apply Nat.mod_divide in Hmod; [|assumption].
  destruct Hmod as [q Hq].
  exists (k*q).
  nia.
Qed.

Lemma tok_at_period_mod b n d:
  b.(b_mu) <= n ->
  b.(b_p) <> O ->
  d mod b.(b_p) = O ->
  tok_at b (n+d) = tok_at b n.
Proof.
  intros Hmu Hp Hmod.
  unfold tok_at.
  destruct (n <? b.(b_mu)) eqn:Hn.
  - apply Nat.ltb_lt in Hn.
    lia.
  - destruct (n+d <? b.(b_mu)) eqn:Hnd.
    + apply Nat.ltb_lt in Hnd.
      lia.
    + f_equal.
      replace (n+d-b.(b_mu)) with (n-b.(b_mu)+d) by lia.
      rewrite Nat.add_mod by exact Hp.
      rewrite Hmod, Nat.add_0_r.
      rewrite Nat.mod_mod by exact Hp.
      reflexivity.
Qed.

Lemma pair_at_period_mod b k shift:
  pair_pre_len b <= k ->
  b.(b_p) <> O ->
  (shift*2) mod b.(b_p) = O ->
  pair_at b (k+shift) = pair_at b k.
Proof.
  intros Hpre Hp Hmod.
  unfold pair_at.
  f_equal.
  - replace ((k+shift)*2) with (k*2+shift*2) by lia.
    apply tok_at_period_mod; auto.
    eapply pair_pre_len_bound.
    exact Hpre.
  - replace (S ((k+shift)*2)) with (S (k*2)+shift*2) by lia.
    apply tok_at_period_mod; auto.
    pose proof (pair_pre_len_bound b k Hpre).
    lia.
Qed.

Lemma pair_list_period_shift b off len shift:
  pair_pre_len b <= off ->
  b.(b_p) <> O ->
  (shift*2) mod b.(b_p) = O ->
  pair_list b (off+shift) len = pair_list b off len.
Proof.
  revert off.
  induction len; intros off Hpre Hp Hmod; cbn.
  - reflexivity.
  - rewrite (pair_at_period_mod b off shift Hpre Hp Hmod).
    f_equal.
    replace (S (off+shift)) with (S off+shift) by lia.
    apply IHlen; auto.
Qed.

Lemma pair_list_period_repeat b off len k:
  pair_pre_len b <= off ->
  b.(b_p) = pair_per_len b*2 ->
  pair_per_len b <> O ->
  len mod pair_per_len b = O ->
  pair_list b (off+k*len) len = pair_list b off len.
Proof.
  intros Hpre Hp Hper Hmod.
  apply pair_list_period_shift; auto.
  - lia.
  - eapply period_shift_mod; eauto.
Qed.

Lemma row_cert_at_prefix_seg i addL addR w:
  row_cert_at i addL addR w = true ->
  segRLs_n tm (src_prefix i addL) (tgt_prefix i addR) [S0] w 1.
Proof.
  unfold row_cert_at, src_prefix, tgt_prefix, src_off, tgt_off,
    row_L0, row_R0, row_dL, row_dR, row_target.
  destruct (row_at i) as [[[[[j l0] r0] vis] dL] dR].
  cbv beta iota zeta.
  intro H.
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [Hprefix _].
  eapply segRLs_n1_c_spec.
  exact Hprefix.
Qed.

Lemma row_cert_at_loop_seg i addL addR w:
  row_cert_at i addL addR w = true ->
  segRLs_n tm (src_loop i addL) (tgt_loop i addR) w w 1.
Proof.
  unfold row_cert_at, src_loop, tgt_loop, src_off, tgt_off, src_len, tgt_len,
    row_L0, row_R0, row_dL, row_dR, row_target.
  destruct (row_at i) as [[[[[j l0] r0] vis] dL] dR].
  cbv beta iota zeta.
  intro H.
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [_ Hloop].
  eapply segRLs_n1_c_spec.
  exact Hloop.
Qed.

Lemma row_cert_at_params i addL addR w:
  row_cert_at i addL addR w = true ->
  pair_pre_len (boundary i) <= src_off i addL /\
  pair_pre_len (boundary (row_target i)) <= tgt_off i addR /\
  O < src_len i /\
  O < tgt_len i /\
  pair_per_len (boundary i) <> O /\
  pair_per_len (boundary (row_target i)) <> O /\
  (boundary i).(b_p) = pair_per_len (boundary i)*2 /\
  (boundary (row_target i)).(b_p) =
    pair_per_len (boundary (row_target i))*2 /\
  src_len i mod pair_per_len (boundary i) = O /\
  tgt_len i mod pair_per_len (boundary (row_target i)) = O.
Proof.
  unfold row_cert_at, src_off, tgt_off, src_len, tgt_len,
    row_L0, row_R0, row_dL, row_dR, row_target.
  destruct (row_at i) as [[[[[j l0] r0] vis] dL] dR].
  cbv beta iota zeta.
  intro H.
  apply andb_true_iff in H as [HpreL H].
  apply andb_true_iff in H as [HpreR H].
  apply andb_true_iff in H as [HlenL H].
  apply andb_true_iff in H as [HlenR H].
  apply andb_true_iff in H as [HperL H].
  apply andb_true_iff in H as [HperR H].
  apply andb_true_iff in H as [HevenL H].
  apply andb_true_iff in H as [HevenR H].
  apply andb_true_iff in H as [HmodL H].
  apply andb_true_iff in H as [HmodR _].
  apply Nat.leb_le in HpreL.
  apply Nat.leb_le in HpreR.
  apply Nat.ltb_lt in HlenL.
  apply Nat.ltb_lt in HlenR.
  apply Nat.ltb_lt in HperL.
  apply Nat.ltb_lt in HperR.
  apply Nat.eqb_eq in HevenL.
  apply Nat.eqb_eq in HevenR.
  apply Nat.eqb_eq in HmodL.
  apply Nat.eqb_eq in HmodR.
  repeat split; try assumption; try lia.
  - apply pair_period_double.
    exact HevenL.
  - apply pair_period_double.
    exact HevenR.
Qed.

Lemma row_tail_downRect i addL addR w:
  row_cert_at i addL addR w = true ->
  downRect tm
    (pair_stream_from (boundary i) (src_off i addL))
    (pair_stream_from (boundary (row_target i)) (tgt_off i addR))
    w 1.
Proof.
  intro Hcert.
  destruct (row_cert_at_params i addL addR w Hcert)
    as [HpreL [HpreR [HlenL [HlenR [HperL [HperR
       [HpL [HpR [HmodL HmodR]]]]]]]]].
  eapply segRLs_n_inf_trans with
    (P := fun L R top => exists k,
      L = pair_stream_from (boundary i) (src_off i addL + k*src_len i) /\
      R = pair_stream_from (boundary (row_target i))
            (tgt_off i addR + k*tgt_len i) /\
      top = w).
  - intros L R top [k [HL [HR Htop]]].
    subst L R top.
    exists
      (pair_list (boundary i) (src_off i addL + k*src_len i) (src_len i)),
      (pair_list (boundary (row_target i))
        (tgt_off i addR + k*tgt_len i) (tgt_len i)),
      w,
      (pair_stream_from (boundary i)
        (src_off i addL + k*src_len i + src_len i)),
      (pair_stream_from (boundary (row_target i))
        (tgt_off i addR + k*tgt_len i + tgt_len i)).
    split.
    + rewrite pair_list_length.
      exact HlenR.
    + split.
      * rewrite (pair_stream_split (boundary i)
          (src_off i addL + k*src_len i) (src_len i)).
        reflexivity.
      * split.
        -- rewrite (pair_stream_split (boundary (row_target i))
             (tgt_off i addR + k*tgt_len i) (tgt_len i)).
           reflexivity.
        -- split.
           ++ rewrite (pair_list_period_repeat (boundary i)
                (src_off i addL) (src_len i) k HpreL HpL HperL HmodL).
              rewrite (pair_list_period_repeat (boundary (row_target i))
                (tgt_off i addR) (tgt_len i) k HpreR HpR HperR HmodR).
              eapply row_cert_at_loop_seg.
              exact Hcert.
           ++ exists (S k).
              split.
              {
                replace (src_off i addL + S k*src_len i)
                   with (src_off i addL + k*src_len i + src_len i) by lia.
                reflexivity.
              }
              split.
              {
                replace (tgt_off i addR + S k*tgt_len i)
                      with (tgt_off i addR + k*tgt_len i + tgt_len i) by lia.
                reflexivity.
              }
              reflexivity.
  - exists O.
    split.
    + replace (src_off i addL + O*src_len i) with (src_off i addL) by lia.
      reflexivity.
    + split.
      * replace (tgt_off i addR + O*tgt_len i) with (tgt_off i addR) by lia.
        reflexivity.
      * reflexivity.
Qed.

Lemma row_downRect_from_cert i addL addR w:
  row_cert_at i addL addR w = true ->
  downRect tm
    (true_boundary_stream i)
    (true_boundary_stream (row_target i))
    [S0] 1.
Proof.
  intro Hcert.
  unfold true_boundary_stream.
  rewrite (pair_stream_split (boundary i) O (src_off i addL)).
  rewrite (pair_stream_split (boundary (row_target i)) O (tgt_off i addR)).
  replace (O + src_off i addL) with (src_off i addL) by lia.
  replace (O + tgt_off i addR) with (tgt_off i addR) by lia.
  eapply segRLs_n_downRect_trans.
  - eapply row_cert_at_prefix_seg.
    exact Hcert.
  - eapply row_tail_downRect.
    exact Hcert.
Qed.

Definition row_target_member i :=
  existsb (Nat.eqb (row_target i)) (seq O 161).

Definition rows_target_ok :=
  forallb row_target_member (seq O 161).

Lemma rows_target_ok_true:
  rows_target_ok = true.
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma row_target_in i:
  In i (seq O 161) ->
  In (row_target i) (seq O 161).
Proof.
  intro Hin.
  pose proof rows_target_ok_true as Hok.
  unfold rows_target_ok in Hok.
  eapply forallb_in in Hok; [|exact Hin].
  unfold row_target_member in Hok.
  apply existsb_exists in Hok as [j [Hj Heq]].
  apply Nat.eqb_eq in Heq.
  subst j.
  exact Hj.
Qed.

Lemma row_choice_some i:
  In i (seq O 161) ->
  exists addL addR w, row_choice i = Some (addL,addR,w).
Proof.
  intro Hin.
  pose proof rows_ok_true as Hok.
  unfold rows_ok in Hok.
  eapply forallb_in in Hok; [|exact Hin].
  unfold row_cert in Hok.
  destruct (row_choice i) as [[[addL addR] w]|] eqn:Hchoice;
    cbn in Hok; try discriminate.
  exists addL, addR, w.
  reflexivity.
Qed.

Lemma right_quadRect:
  quadRect tm (true_boundary_stream O) (const S0).
Proof.
  eapply downRect_inf_concat with
    (P := fun L top =>
      exists i, In i (seq O 161) /\
        L = true_boundary_stream i /\
        top = const S0).
  - intros L top [i [Hin [HL Htop]]].
    subst L top.
    destruct (row_choice_some i Hin) as [addL [addR [bot Hchoice]]].
    pose proof (row_choice_spec i addL addR bot Hchoice) as Hcert.
    exists (true_boundary_stream (row_target i)), (const S0), [S0], 1.
    split; [lia|].
    split.
    + cbn; rewrite <- const_unfold; reflexivity.
    + split.
      * eapply row_downRect_from_cert.
        exact Hcert.
      * exists (row_target i).
        split.
        -- apply row_target_in.
           exact Hin.
        -- split; reflexivity.
  - exists O.
    split.
    + cbn; auto.
    + split; reflexivity.
Qed.

Fixpoint link_pairs (hs : list (DH0*DH0)) (h : DH0) : list (DH0*DH0) :=
  match hs with
  | [] => []
  | p::rest =>
      match rest with
      | [] => [(snd p,h)]
      | q::_ => (snd p,fst q)::link_pairs rest h
      end
  end.

Definition left_start : DH0 := (E,[]).
Definition left_loop_head : DH0 := (A,[]).
Definition left_entry_side : side := [S0;S1;S1] *> const S0.
Definition left_after n : side := ([S0;S0] ++ [S1]^^(9+n*2)) *> const S0.

Definition left_prefix_pairs := pair_list B0 O 8.
Definition left_loop_pairs := pair_list B0 8 3.
Definition left_prefix_crossings :=
  link_pairs left_prefix_pairs left_loop_head.
Definition left_period :=
  link_pairs left_loop_pairs left_loop_head.

Lemma left_prefix_lcons:
  lcons left_start left_prefix_crossings =
  (left_prefix_pairs,left_loop_head).
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma left_loop_lcons:
  lcons left_loop_head left_period =
  (left_loop_pairs,left_loop_head).
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma left_prefix_side:
  sideRLs (flip tm) left_prefix_crossings left_entry_side (left_after O).
Proof.
  eapply sideRLs_c_spec with (r' := left_after O) (T := 1000).
  - native_compute.
    reflexivity.
  - reflexivity.
Qed.

Lemma left_period_side n:
  sideRLs (flip tm) left_period (left_after n) (left_after (S n)).
Proof.
  unfold left_period, left_loop_pairs, left_loop_head, left_after, link_pairs.
  cbn.
  esx.
Qed.

Lemma B0_loop_split n:
  pair_stream_from B0 (8+n*3) =
  left_loop_pairs *> pair_stream_from B0 (8+S n*3).
Proof.
  rewrite (pair_stream_split B0 (8+n*3) 3).
  replace (8+n*3+3) with (8+S n*3) by lia.
  unfold left_loop_pairs.
  rewrite (pair_list_period_repeat B0 8 3 n).
  - reflexivity.
  - native_compute.
    lia.
  - native_compute.
    reflexivity.
  - native_compute.
    lia.
  - native_compute.
    reflexivity.
Qed.

Lemma left_tail_realizes:
  leftRealizes tm left_loop_head (pair_stream_from B0 8) (left_after O).
Proof.
  eapply leftRealizes_inf_concat with
    (P := fun h L l =>
      exists n, h = left_loop_head /\
        L = pair_stream_from B0 (8+n*3) /\
        l = left_after n).
  - intros h L l [n [Hh [HL Hl]]].
    subst h L l.
    exists left_loop_pairs,
      (pair_stream_from B0 (8+S n*3)),
      left_loop_head,
      left_period,
      (left_after (S n)).
    split.
    + native_compute.
      lia.
    + split.
      * apply B0_loop_split.
      * split.
        -- apply left_loop_lcons.
        -- split.
           ++ apply left_period_side.
           ++ exists (S n).
              repeat split; reflexivity.
  - exists O.
    repeat split; reflexivity.
Qed.

Lemma left_realizes:
  leftRealizes tm left_start (true_boundary_stream O) left_entry_side.
Proof.
  unfold true_boundary_stream.
  rewrite boundary0.
  rewrite (pair_stream_split B0 O 8).
  replace (O+8) with 8 by lia.
  eapply sideRLs_leftRealizes_trans.
  - apply left_prefix_lcons.
  - apply left_prefix_side.
  - apply left_tail_realizes.
Qed.

Lemma entry_progress:
  c0 -[ tm ]->+ left_entry_side {{{ (left_start,R) }}} const S0.
Proof.
  unfold left_entry_side, left_start.
  execute.
Qed.

Lemma entry_nonhalt:
  ~halts tm (left_entry_side {{{ (left_start,R) }}} const S0).
Proof.
  eapply quadRect_nonhalt.
  - apply right_quadRect.
  - apply left_realizes.
Qed.

Lemma nonhalt:
  ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply progress_evstep.
    apply entry_progress.
  - apply entry_nonhalt.
Qed.

End TM4.
