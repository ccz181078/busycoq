From BusyCoq Require Import
  Individual62 Longitudinal LongN InfiniteRect ES_v3.
Require Import Lia List String Ascii.

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RD_0LD0LB_1RA1LE_0LC1LF_0LA---").

Notation hxa := ((A,[0;0]),(D,@nil Sym)).
Notation hq := ((D,[0;1;1;0]),(D,@nil Sym)).

Definition C0 n : list Sym := ([0;1]^^n) ++ [0;0;1].
Definition C1 n : list Sym := ([0;1]^^n) ++ [0;1;1].
Definition E n : side := ([0;1]^^n) *> 0inf.

Lemma p_E0_gen k:
  segRLs_n tm [hxa] [] (C0 (k*2)) (C1 (k*2+1)) 1.
Proof.
  unfold C0, C1; st.
  solve_segRLs_n.
Qed.

Lemma p_E1_gen k:
  segRLs_n tm [hxa] [] (C1 (k*2)) (C0 (k*2+1)) 1.
Proof.
  unfold C0, C1; st.
  solve_segRLs_n.
Qed.

Lemma p_O0_gen k:
  segRLs_n tm [hxa] [hq] (C0 (k*2+3)) (C0 (k*2+2)) 1.
Proof.
  unfold C0, C1; st.
  solve_segRLs_n.
Qed.

Lemma q_E0_gen k:
  segRLs_n tm [hq] [hq] (C0 (S k*2)) (C1 (S k*2)) 1.
Proof.
  unfold C0, C1; st.
  solve_segRLs_n.
Qed.

Lemma q_E1_gen k:
  segRLs_n tm [hq] [hxa;hq]
    (C1 (k*2+2)) (C0 (k*2+1)) 1.
Proof.
  unfold C0, C1; st.
  solve_segRLs_n.
Qed.

Lemma q_O0_gen k:
  segRLs_n tm [hq] [hxa] (C0 (k*2+3)) (C0 (k*2+4)) 1.
Proof.
  unfold C0, C1; st.
  solve_segRLs_n.
Qed.

Lemma q_O1_gen k:
  segRLs_n tm [hq] [hq] (C1 (k*2+1)) (C0 (k*2+1)) 1.
Proof.
  unfold C0, C1; st.
  solve_segRLs_n.
Qed.

Inductive signal := P | Qs.

Definition signal_head (s:signal) : DH0*DH0 :=
  match s with P => hxa | Qs => hq end.

CoFixpoint signal_heads (L:Stream signal) : Stream (DH0*DH0) :=
  Cons (signal_head (Streams.hd L)) (signal_heads (Streams.tl L)).

CoInductive good : nat -> Stream signal -> Prop :=
| good0 L : good 1 L -> good 0 (Cons Qs L)
| good1P L : good 0 L -> good 1 (Cons P L)
| good1Q L : good 2 L -> good 1 (Cons Qs L)
| good2 L : good 3 L -> good 2 (Cons Qs L)
| good3 L : good 0 L -> good 3 (Cons P L).

Inductive relstate :=
| R000 | R002 | R013 | R021 | R023 | R030
| R100 | R111 | R113 | R121
| R200 | R211 | R221 | R300 | R311 | R321.

Definition in_phase (s:relstate) : nat :=
  match s with
  | R000 | R002 | R013 | R021 | R023 | R030 => 0
  | R100 | R111 | R113 | R121 => 1
  | R200 | R211 | R221 => 2
  | R300 | R311 | R321 => 3
  end.

Definition out_phase (s:relstate) : nat :=
  match s with
  | R000 | R030 | R100 | R200 | R300 => 0
  | R013 | R023 | R113 => 3
  | R021 | R111 | R121 | R211 | R221 | R311 | R321 => 1
  | R002 => 2
  end.

Definition column (s:relstate) (k:nat) : list Sym :=
  match s with
  | R000 | R002 => C0 (2+2*k)
  | R013 => C1 (4+2*k)
  | R021 | R023 => C0 (3+2*k)
  | R030 => C1 (3+2*k)
  | R100 => C0 (4+2*k)
  | R111 | R113 => C1 (2+2*k)
  | R121 => C0 (3+2*k)
  | R200 => C0 (2+2*k)
  | R211 => C1 (4+2*k)
  | R221 => C0 (1+2*k)
  | R300 => C0 (2+2*k)
  | R311 => C1 (2+2*k)
  | R321 => C0 (3+2*k)
  end.

CoFixpoint transduce (s:relstate) (L:Stream signal) : Stream signal :=
  match s with
  | R000 => Cons Qs (transduce R111 (Streams.tl L))
  | R002 => Cons Qs (transduce R113 (Streams.tl L))
  | R013 => Cons P (Cons Qs (transduce R121 (Streams.tl L)))
  | R021 | R023 => Cons P (transduce R100 (Streams.tl L))
  | R030 => Cons Qs (transduce R121 (Streams.tl L))
  | R100 =>
      match Streams.hd L with
      | P => Cons Qs (transduce R121 (Streams.tl (Streams.tl L)))
      | Qs => Cons Qs (transduce R211 (Streams.tl L))
      end
  | R111 | R113 =>
      match Streams.hd L with
      | P => Cons P (transduce R100 (Streams.tl (Streams.tl L)))
      | Qs => Cons P (Cons Qs (transduce R221 (Streams.tl L)))
      end
  | R121 =>
      match Streams.hd L with
      | P => Cons Qs (transduce R002 (Streams.tl L))
      | Qs => Cons P (transduce R200 (Streams.tl L))
      end
  | R200 => Cons Qs (transduce R311 (Streams.tl L))
  | R211 => Cons P (Cons Qs (transduce R321 (Streams.tl L)))
  | R221 => Cons P (transduce R300 (Streams.tl L))
  | R300 => Cons Qs (transduce R121 (Streams.tl (Streams.tl L)))
  | R311 => Cons P (transduce R100 (Streams.tl (Streams.tl L)))
  | R321 => Cons Qs (transduce R002 (Streams.tl L))
  end.

Lemma good0_inv L: good 0 L ->
  exists T, L = Cons Qs T /\ good 1 T.
Proof. inversion 1; subst; eauto. Qed.

Lemma good1_inv L: good 1 L ->
  (exists T, L = Cons P T /\ good 0 T) \/
  (exists T, L = Cons Qs T /\ good 2 T).
Proof. inversion 1; subst; eauto. Qed.

Lemma good2_inv L: good 2 L ->
  exists T, L = Cons Qs T /\ good 3 T.
Proof. inversion 1; subst; eauto. Qed.

Lemma good3_inv L: good 3 L ->
  exists T, L = Cons P T /\ good 0 T.
Proof. inversion 1; subst; eauto. Qed.

Ltac unfold_transduce :=
  match goal with
  | |- context [transduce ?s ?L] =>
      rewrite (unfold_Stream (transduce s L));
      cbn [transduce Streams.hd Streams.tl]
  end.

Lemma transduce_good s L:
  good (in_phase s) L -> good (out_phase s) (transduce s L).
Proof.
  revert s L; cofix CH; intros s L HG; destruct s.
  - destruct (good0_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 0 (Cons Qs (transduce R111 T))).
    apply good0; exact (CH R111 T HT).
  - destruct (good0_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 2 (Cons Qs (transduce R113 T))).
    apply good2; exact (CH R113 T HT).
  - destruct (good0_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 3 (Cons P (Cons Qs (transduce R121 T)))).
    apply good3; apply good0; exact (CH R121 T HT).
  - destruct (good0_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 1 (Cons P (transduce R100 T))).
    apply good1P; exact (CH R100 T HT).
  - destruct (good0_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 3 (Cons P (transduce R100 T))).
    apply good3; exact (CH R100 T HT).
  - destruct (good0_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 0 (Cons Qs (transduce R121 T))).
    apply good0; exact (CH R121 T HT).
  - destruct (good1_inv _ HG) as [[T [-> HT]]|[T [-> HT]]].
    + destruct (good0_inv _ HT) as [U [-> HU]].
      unfold_transduce.
      change (good 0 (Cons Qs (transduce R121 U))).
      apply good0; exact (CH R121 U HU).
    + unfold_transduce.
      change (good 0 (Cons Qs (transduce R211 T))).
      apply good0; exact (CH R211 T HT).
  - destruct (good1_inv _ HG) as [[T [-> HT]]|[T [-> HT]]].
    + destruct (good0_inv _ HT) as [U [-> HU]].
      unfold_transduce.
      change (good 1 (Cons P (transduce R100 U))).
      apply good1P; exact (CH R100 U HU).
    + unfold_transduce.
      change (good 1 (Cons P (Cons Qs (transduce R221 T)))).
      apply good1P; apply good0; exact (CH R221 T HT).
  - destruct (good1_inv _ HG) as [[T [-> HT]]|[T [-> HT]]].
    + destruct (good0_inv _ HT) as [U [-> HU]].
      unfold_transduce.
      change (good 3 (Cons P (transduce R100 U))).
      apply good3; exact (CH R100 U HU).
    + unfold_transduce.
      change (good 3 (Cons P (Cons Qs (transduce R221 T)))).
      apply good3; apply good0; exact (CH R221 T HT).
  - destruct (good1_inv _ HG) as [[T [-> HT]]|[T [-> HT]]].
    + unfold_transduce. change (good 1 (Cons Qs (transduce R002 T))).
      apply good1Q; exact (CH R002 T HT).
    + unfold_transduce. change (good 1 (Cons P (transduce R200 T))).
      apply good1P; exact (CH R200 T HT).
  - destruct (good2_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 0 (Cons Qs (transduce R311 T))).
    apply good0; exact (CH R311 T HT).
  - destruct (good2_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 1 (Cons P (Cons Qs (transduce R321 T)))).
    apply good1P; apply good0; exact (CH R321 T HT).
  - destruct (good2_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 1 (Cons P (transduce R300 T))).
    apply good1P; exact (CH R300 T HT).
  - destruct (good3_inv _ HG) as [T [-> HT]].
    destruct (good0_inv _ HT) as [U [-> HU]].
    unfold_transduce.
    change (good 0 (Cons Qs (transduce R121 U))).
    apply good0; exact (CH R121 U HU).
  - destruct (good3_inv _ HG) as [T [-> HT]].
    destruct (good0_inv _ HT) as [U [-> HU]].
    unfold_transduce.
    change (good 1 (Cons P (transduce R100 U))).
    apply good1P; exact (CH R100 U HU).
  - destruct (good3_inv _ HG) as [T [-> HT]].
    unfold_transduce.
    change (good 1 (Cons Qs (transduce R002 T))).
    apply good1Q; exact (CH R002 T HT).
Qed.

Lemma local_R000 k:
  segRLs_n tm [hq] [hq] (column R000 k) (column R111 k) 1.
Proof. cbn [column]. replace (2+2*k) with (S k*2) by lia. apply q_E0_gen. Qed.

Lemma local_R002 k:
  segRLs_n tm [hq] [hq] (column R002 k) (column R113 k) 1.
Proof. cbn [column]. replace (2+2*k) with (S k*2) by lia. apply q_E0_gen. Qed.

Lemma local_R013 k:
  segRLs_n tm [hq] [hxa;hq] (column R013 k) (column R121 k) 1.
Proof.
  cbn [column].
  replace (4+2*k) with (S k*2+2) by lia.
  replace (3+2*k) with (S k*2+1) by lia.
  apply q_E1_gen.
Qed.

Lemma local_R021 k:
  segRLs_n tm [hq] [hxa] (column R021 k) (column R100 k) 1.
Proof. cbn [column]. applys_eq (q_O0_gen k); f_equal; lia. Qed.

Lemma local_R023 k:
  segRLs_n tm [hq] [hxa] (column R023 k) (column R100 k) 1.
Proof. cbn [column]. applys_eq (q_O0_gen k); f_equal; lia. Qed.

Lemma local_R030 k:
  segRLs_n tm [hq] [hq] (column R030 k) (column R121 k) 1.
Proof.
  cbn [column].
  replace (3+2*k) with (S k*2+1) by lia.
  apply q_O1_gen.
Qed.

Lemma local_R100_P k:
  segRLs_n tm [hxa;hq] [hq]
    (column R100 k) (column R121 (S k)) 1.
Proof.
  cbn [column].
  replace (3+2*S k) with (5+2*k) by lia.
  change (segRLs_n tm ([hxa]++[hq]) ([]++[hq])
    (C0 (4+2*k)) (C0 (5+2*k)) 1).
  eapply segRLs_n_trans.
  - replace (4+2*k) with ((k+2)*2) by lia.
    replace (5+2*k) with ((k+2)*2+1) by lia.
    apply p_E0_gen.
  - replace (5+2*k) with ((k+2)*2+1) by lia.
    apply q_O1_gen.
  - lia.
  - lia.
Qed.

Lemma local_R100_Q k:
  segRLs_n tm [hq] [hq] (column R100 k) (column R211 k) 1.
Proof.
  cbn [column].
  replace (4+2*k) with (S (S k)*2) by lia.
  apply q_E0_gen.
Qed.

Lemma local_R111_P k:
  segRLs_n tm [hxa;hq] [hxa]
    (column R111 k) (column R100 k) 1.
Proof.
  cbn [column].
  change (segRLs_n tm ([hxa]++[hq]) ([]++[hxa])
    (C1 (2+2*k)) (C0 (4+2*k)) 1).
  eapply segRLs_n_trans.
  - replace (2+2*k) with (S k*2) by lia.
    replace (3+2*k) with (S k*2+1) by lia.
    apply p_E1_gen.
  - applys_eq (q_O0_gen k); f_equal; lia.
  - lia.
  - lia.
Qed.

Lemma local_R111_Q k:
  segRLs_n tm [hq] [hxa;hq]
    (column R111 k) (column R221 k) 1.
Proof.
  cbn [column].
  replace (2+2*k) with (k*2+2) by lia.
  replace (1+2*k) with (k*2+1) by lia.
  apply q_E1_gen.
Qed.

Lemma local_R113_P k:
  segRLs_n tm [hxa;hq] [hxa]
    (column R113 k) (column R100 k) 1.
Proof. apply local_R111_P. Qed.

Lemma local_R113_Q k:
  segRLs_n tm [hq] [hxa;hq]
    (column R113 k) (column R221 k) 1.
Proof. apply local_R111_Q. Qed.

Lemma local_R121_P k:
  segRLs_n tm [hxa] [hq] (column R121 k) (column R002 k) 1.
Proof. cbn [column]. applys_eq (p_O0_gen k); f_equal; lia. Qed.

Lemma local_R121_Q k:
  segRLs_n tm [hq] [hxa] (column R121 k) (column R200 (S k)) 1.
Proof. cbn [column]. applys_eq (q_O0_gen k); f_equal; lia. Qed.

Lemma local_R200 k:
  segRLs_n tm [hq] [hq] (column R200 k) (column R311 k) 1.
Proof. cbn [column]. replace (2+2*k) with (S k*2) by lia. apply q_E0_gen. Qed.

Lemma local_R211 k:
  segRLs_n tm [hq] [hxa;hq] (column R211 k) (column R321 k) 1.
Proof.
  cbn [column].
  replace (4+2*k) with (S k*2+2) by lia.
  replace (3+2*k) with (S k*2+1) by lia.
  apply q_E1_gen.
Qed.

Lemma q_O0_one:
  segRLs_n tm [hq] [hxa] (C0 1) (C0 2) 1.
Proof. solve_segRLs_n1. Qed.

Lemma local_R221 k:
  segRLs_n tm [hq] [hxa] (column R221 k) (column R300 k) 1.
Proof.
  destruct k as [|k].
  - exact q_O0_one.
  - cbn [column]. applys_eq (q_O0_gen k); f_equal; lia.
Qed.

Lemma local_R300 k:
  segRLs_n tm [hxa;hq] [hq]
    (column R300 k) (column R121 k) 1.
Proof.
  cbn [column].
  change (segRLs_n tm ([hxa]++[hq]) ([]++[hq])
    (C0 (2+2*k)) (C0 (3+2*k)) 1).
  eapply segRLs_n_trans.
  - replace (2+2*k) with (S k*2) by lia.
    replace (3+2*k) with (S k*2+1) by lia.
    apply p_E0_gen.
  - replace (3+2*k) with (S k*2+1) by lia.
    apply q_O1_gen.
  - lia.
  - lia.
Qed.

Lemma local_R311 k:
  segRLs_n tm [hxa;hq] [hxa]
    (column R311 k) (column R100 k) 1.
Proof. apply local_R111_P. Qed.

Lemma local_R321 k:
  segRLs_n tm [hxa] [hq] (column R321 k) (column R002 k) 1.
Proof. cbn [column]. applys_eq (p_O0_gen k); f_equal; lia. Qed.

Lemma signal_heads_cons s L:
  signal_heads (Cons s L) = [signal_head s] *> signal_heads L.
Proof.
  rewrite (unfold_Stream (signal_heads (Cons s L))).
  reflexivity.
Qed.

Lemma signal_heads_cons2 s1 s2 L:
  signal_heads (Cons s1 (Cons s2 L)) =
    [signal_head s1;signal_head s2] *> signal_heads L.
Proof. rewrite signal_heads_cons, signal_heads_cons. reflexivity. Qed.

Inductive flow_state :
    Stream (DH0*DH0) -> Stream (DH0*DH0) -> list Sym -> Prop :=
| flow_here s k L : good (in_phase s) L ->
    flow_state (signal_heads L) (signal_heads (transduce s L)) (column s k).

Lemma column_downRect s k L:
  good (in_phase s) L ->
  downRect tm (signal_heads L) (signal_heads (transduce s L))
    (column s k) 1.
Proof.
  intro HG.
  eapply segRLs_n_inf_trans with (P:=flow_state).
  2: constructor; exact HG.
  intros Lin Rout top HF; inversion HF as [s0 k0 S Hgood]; subst.
  destruct s0.
  - destruct (good0_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hq], (column R111 k0),
      (signal_heads T), (signal_heads (transduce R111 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R000|constructor; exact HT].
  - destruct (good0_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hq], (column R113 k0),
      (signal_heads T), (signal_heads (transduce R113 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R002|constructor; exact HT].
  - destruct (good0_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hxa;hq], (column R121 k0),
      (signal_heads T), (signal_heads (transduce R121 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons2. reflexivity.
    + split; [apply local_R013|constructor; exact HT].
  - destruct (good0_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hxa], (column R100 k0),
      (signal_heads T), (signal_heads (transduce R100 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R021|constructor; exact HT].
  - destruct (good0_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hxa], (column R100 k0),
      (signal_heads T), (signal_heads (transduce R100 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R023|constructor; exact HT].
  - destruct (good0_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hq], (column R121 k0),
      (signal_heads T), (signal_heads (transduce R121 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R030|constructor; exact HT].
  - destruct (good1_inv _ Hgood) as [[T [-> HT]]|[T [-> HT]]].
    + destruct (good0_inv _ HT) as [U [-> HU]].
      exists [hxa;hq], [hq], (column R121 (S k0)),
        (signal_heads U), (signal_heads (transduce R121 U)).
      split; [cbn; lia|]. split; [apply signal_heads_cons2|]. split.
      * unfold_transduce. rewrite signal_heads_cons. reflexivity.
      * split; [apply local_R100_P|constructor; exact HU].
    + exists [hq], [hq], (column R211 k0),
        (signal_heads T), (signal_heads (transduce R211 T)).
      split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
      * unfold_transduce. rewrite signal_heads_cons. reflexivity.
      * split; [apply local_R100_Q|constructor; exact HT].
  - destruct (good1_inv _ Hgood) as [[T [-> HT]]|[T [-> HT]]].
    + destruct (good0_inv _ HT) as [U [-> HU]].
      exists [hxa;hq], [hxa], (column R100 k0),
        (signal_heads U), (signal_heads (transduce R100 U)).
      split; [cbn; lia|]. split; [apply signal_heads_cons2|]. split.
      * unfold_transduce. rewrite signal_heads_cons. reflexivity.
      * split; [apply local_R111_P|constructor; exact HU].
    + exists [hq], [hxa;hq], (column R221 k0),
        (signal_heads T), (signal_heads (transduce R221 T)).
      split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
      * unfold_transduce. rewrite signal_heads_cons2. reflexivity.
      * split; [apply local_R111_Q|constructor; exact HT].
  - destruct (good1_inv _ Hgood) as [[T [-> HT]]|[T [-> HT]]].
    + destruct (good0_inv _ HT) as [U [-> HU]].
      exists [hxa;hq], [hxa], (column R100 k0),
        (signal_heads U), (signal_heads (transduce R100 U)).
      split; [cbn; lia|]. split; [apply signal_heads_cons2|]. split.
      * unfold_transduce. rewrite signal_heads_cons. reflexivity.
      * split; [apply local_R113_P|constructor; exact HU].
    + exists [hq], [hxa;hq], (column R221 k0),
        (signal_heads T), (signal_heads (transduce R221 T)).
      split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
      * unfold_transduce. rewrite signal_heads_cons2. reflexivity.
      * split; [apply local_R113_Q|constructor; exact HT].
  - destruct (good1_inv _ Hgood) as [[T [-> HT]]|[T [-> HT]]].
    + exists [hxa], [hq], (column R002 k0),
        (signal_heads T), (signal_heads (transduce R002 T)).
      split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
      * unfold_transduce. rewrite signal_heads_cons. reflexivity.
      * split; [apply local_R121_P|constructor; exact HT].
    + exists [hq], [hxa], (column R200 (S k0)),
        (signal_heads T), (signal_heads (transduce R200 T)).
      split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
      * unfold_transduce. rewrite signal_heads_cons. reflexivity.
      * split; [apply local_R121_Q|constructor; exact HT].
  - destruct (good2_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hq], (column R311 k0),
      (signal_heads T), (signal_heads (transduce R311 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R200|constructor; exact HT].
  - destruct (good2_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hxa;hq], (column R321 k0),
      (signal_heads T), (signal_heads (transduce R321 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons2. reflexivity.
    + split; [apply local_R211|constructor; exact HT].
  - destruct (good2_inv _ Hgood) as [T [-> HT]].
    exists [hq], [hxa], (column R300 k0),
      (signal_heads T), (signal_heads (transduce R300 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R221|constructor; exact HT].
  - destruct (good3_inv _ Hgood) as [T [-> HT]].
    destruct (good0_inv _ HT) as [U [-> HU]].
    exists [hxa;hq], [hq], (column R121 k0),
      (signal_heads U), (signal_heads (transduce R121 U)).
    split; [cbn; lia|]. split; [apply signal_heads_cons2|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R300|constructor; exact HU].
  - destruct (good3_inv _ Hgood) as [T [-> HT]].
    destruct (good0_inv _ HT) as [U [-> HU]].
    exists [hxa;hq], [hxa], (column R100 k0),
      (signal_heads U), (signal_heads (transduce R100 U)).
    split; [cbn; lia|]. split; [apply signal_heads_cons2|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R311|constructor; exact HU].
  - destruct (good3_inv _ Hgood) as [T [-> HT]].
    exists [hxa], [hq], (column R002 k0),
      (signal_heads T), (signal_heads (transduce R002 T)).
    split; [cbn; lia|]. split; [apply signal_heads_cons|]. split.
    + unfold_transduce. rewrite signal_heads_cons. reflexivity.
    + split; [apply local_R321|constructor; exact HT].
Qed.

Lemma edge_short:
  sideRLs tm [hq;hxa] (E 3) (C0 6 *> E 3).
Proof.
  unfold E, C0.
  eapply sideRLs_c_spec with (T:=100000).
  - vm_compute; reflexivity.
  - st; reflexivity.
Qed.

Lemma edge_long:
  sideRLs tm [hq;hq;hq;hxa] (E 3) (C0 14 *> E 3).
Proof.
  unfold E, C0.
  eapply sideRLs_c_spec with (T:=100000).
  - vm_compute; reflexivity.
  - st; reflexivity.
Qed.

Definition dynamic_side_step tm
    (X : Stream (DH0*DH0) -> side -> Prop)
    (L : Stream (DH0*DH0)) (top : side) : Prop :=
  exists hs Ltail Ledge top' w width,
    0 < width /\ w <> [] /\ L = hs *> Ltail /\
    sideRLs tm hs top (w *> top') /\
    downRect tm Ltail Ledge w width /\ X Ledge top'.

Lemma dynamic_side_unbounded tm0 X L top:
  (forall L0 top0, X L0 top0 -> dynamic_side_step tm0 X L0 top0) ->
  X L top -> quadRect tm0 L top.
Proof.
  intros Hstep HX.
  unfold quadRect, InfiniteRectInternal.quadRect.
  assert (Hn : forall n L0 top0, X L0 top0 ->
      @InfiniteRectInternal.sideS_n tm0 L0 top0 n).
  {
    induction n as [|n IH]; intros L0 top0 HX0.
    - apply InfiniteRectInternal.sideS_n_0.
    - destruct (Hstep _ _ HX0) as
        (hs & Ltail & Ledge & top' & w & width &
         Hwidth & Hw & HL & Hedge & Hrect & HX').
      specialize (IH _ _ HX').
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

Definition edge_cycle (L:Stream (DH0*DH0)) (top:side) : Prop :=
  exists S, good 0 S /\ L = signal_heads S /\ top = E 3.

Lemma edge_cycle_step L top:
  edge_cycle L top -> dynamic_side_step tm edge_cycle L top.
Proof.
  intros [S [HG [-> ->]]].
  destruct (good0_inv _ HG) as [T [-> HT]].
  destruct (good1_inv _ HT) as [[U [-> HU]]|[U [-> HU]]].
  - exists [hq;hxa], (signal_heads U),
      (signal_heads (transduce R000 U)), (E 3), (C0 6), 1%nat.
    split; [lia|]. split; [discriminate|]. split.
    + apply signal_heads_cons2.
    + split; [apply edge_short|]. split.
      * change (downRect tm (signal_heads U)
          (signal_heads (transduce R000 U)) (column R000 2) 1).
        apply column_downRect; exact HU.
      * exists (transduce R000 U). split.
        -- exact (transduce_good R000 U HU).
        -- split; reflexivity.
  - destruct (good2_inv _ HU) as [V [-> HV]].
    destruct (good3_inv _ HV) as [W [-> HW]].
    exists [hq;hq;hq;hxa], (signal_heads W),
      (signal_heads (transduce R000 W)), (E 3), (C0 14), 1%nat.
    split; [lia|]. split; [discriminate|]. split.
    + repeat rewrite signal_heads_cons. reflexivity.
    + split; [apply edge_long|]. split.
      * change (downRect tm (signal_heads W)
          (signal_heads (transduce R000 W)) (column R000 6) 1).
        apply column_downRect; exact HW.
      * exists (transduce R000 W). split.
        -- exact (transduce_good R000 W HW).
        -- split; reflexivity.
Qed.

Lemma edge_cycle_quadRect L top:
  edge_cycle L top -> quadRect tm L top.
Proof.
  apply dynamic_side_unbounded, edge_cycle_step.
Qed.

Lemma sideRLs_downRect_quadRect tm0 hs Ltail Ledge top top' w width:
  0 < width ->
  sideRLs tm0 hs top (w *> top') ->
  downRect tm0 Ltail Ledge w width ->
  quadRect tm0 Ledge top' ->
  quadRect tm0 (hs *> Ltail) top.
Proof.
  intros Hwidth Hedge Hrect Hnext.
  assert (Hword:quadRect tm0 Ltail (w *> top')).
  { eapply downRect_quadRect_concat; eauto. }
  unfold quadRect, InfiniteRectInternal.quadRect in *.
  intro n.
  eapply InfiniteRectInternal.sideS_n_app_right;
    [exact Hedge|exact (Hword n)].
Qed.

Notation hxaR := (A,[0;0]).
Notation hxaL := (D,@nil Sym).
Notation hxaLR := [(hxaL,hxaR)].

Definition left_p (n:nat) : side :=
  ([1] ++ ([0;1]^^n)) *> 0inf.

Lemma left_p_loop k:
  sideRLs (flip tm) hxaLR (left_p (k*2)) (left_p (k*2)).
Proof.
  unfold left_p.
  repeat rewrite (lpow_mul [0;1] k 2).
  cbn [lpow].
  solve_sideRLs; es.
Qed.

CoFixpoint pq_stream : Stream signal := Cons P (Cons Qs pq_stream).
CoFixpoint qp_stream : Stream signal := Cons Qs (Cons P qp_stream).
CoFixpoint hp_stream : Stream (DH0*DH0) := Cons hxa hp_stream.

Lemma pq_stream_unfold: pq_stream = Cons P (Cons Qs pq_stream).
Proof. rewrite (unfold_Stream pq_stream) at 1; reflexivity. Qed.
Lemma qp_stream_unfold: qp_stream = Cons Qs (Cons P qp_stream).
Proof. rewrite (unfold_Stream qp_stream) at 1; reflexivity. Qed.
Lemma hp_stream_unfold: hp_stream = Cons hxa hp_stream.
Proof. rewrite (unfold_Stream hp_stream) at 1; reflexivity. Qed.

Lemma hp_stream_three:
  hp_stream = [hxa;hxa;hxa] *> hp_stream.
Proof.
  rewrite hp_stream_unfold at 1.
  rewrite hp_stream_unfold at 1.
  rewrite hp_stream_unfold at 1.
  reflexivity.
Qed.

Lemma pq_heads_two:
  signal_heads pq_stream = [hxa;hq] *> signal_heads pq_stream.
Proof.
  rewrite pq_stream_unfold at 1.
  apply signal_heads_cons2.
Qed.

Lemma pq_good: good 1 pq_stream.
Proof.
  cofix CH. rewrite pq_stream_unfold.
  apply good1P, good0, CH.
Qed.

Lemma qp_good: good 0 qp_stream.
Proof.
  cofix CH. rewrite qp_stream_unfold.
  apply good0, good1P, CH.
Qed.

Lemma C16_p_period:
  segRLs_n tm [hxa;hxa;hxa] [hxa;hq] (C0 16) (C0 16) 1.
Proof. solve_segRLs_n1_with 100000. Qed.

Lemma C16_p_downRect:
  downRect tm hp_stream (signal_heads pq_stream) (C0 16) 1.
Proof.
  eapply segRLs_n_inf_trans with
    (P:=fun L R w =>
      L = hp_stream /\ R = signal_heads pq_stream /\ w = C0 16).
  - intros L R w [-> [-> ->]].
    exists [hxa;hxa;hxa], [hxa;hq], (C0 16),
      hp_stream, (signal_heads pq_stream).
    split; [cbn; lia|]. split.
    + apply hp_stream_three.
    + split.
      * apply pq_heads_two.
      * split; [apply C16_p_period|repeat split; reflexivity].
  - repeat split; reflexivity.
Qed.

Lemma p_stream_realizes:
  leftRealizes tm hxaR hp_stream (left_p 18).
Proof.
  eapply leftRealizes_inf_concat with
    (P:=fun h L l =>
      h = hxaR /\ L = hp_stream /\ l = left_p 18).
  - intros h L l [-> [-> ->]].
    exists [hxa], hp_stream, hxaR, hxaLR, (left_p 18).
    split; [cbn; lia|]. split.
    + apply hp_stream_unfold.
    + split; [reflexivity|]. split.
      * replace 18 with (9*2) by lia. apply left_p_loop.
      * repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.

Definition bl5_suffix_word : list Sym :=
  C1 14 ++ C0 11 ++ C0 7 ++ C0 8 ++ C0 6 ++
  C1 8 ++ C1 6 ++ C0 7 ++ C0 8 ++ C0 6 ++
  C1 8 ++ C1 6 ++ C0 7 ++ C0 8 ++ C0 6 ++
  C1 8 ++ C1 6 ++ C0 7 ++ C0 8 ++ C0 6.

Ltac next_column st k Hin Hout :=
  eapply downRect_quadRect_concat;
  [exact (column_downRect st k _ Hin)|];
  pose proof (transduce_good st _ Hin) as Hout;
  cbn [out_phase] in Hout.

Lemma bl5_suffix_quadRect:
  quadRect tm (signal_heads pq_stream) (bl5_suffix_word *> E 3).
Proof.
  unfold bl5_suffix_word; repeat rewrite Str_app_assoc.
  pose proof pq_good as H0.
  next_column R113 6 H0 H1.
  next_column R321 4 H1 H2.
  next_column R121 2 H2 H3.
  next_column R100 2 H3 H4.
  next_column R000 2 H4 H5.
  next_column R013 2 H5 H6.
  next_column R311 2 H6 H7.
  next_column R121 2 H7 H8.
  next_column R100 2 H8 H9.
  next_column R000 2 H9 H10.
  next_column R013 2 H10 H11.
  next_column R311 2 H11 H12.
  next_column R121 2 H12 H13.
  next_column R100 2 H13 H14.
  next_column R000 2 H14 H15.
  next_column R013 2 H15 H16.
  next_column R311 2 H16 H17.
  next_column R121 2 H17 H18.
  next_column R100 2 H18 H19.
  next_column R000 2 H19 H20.
  apply edge_cycle_quadRect.
  eexists; split; [exact H20|split; reflexivity].
Qed.

Definition bl5_cut_top : side := C0 16 *> bl5_suffix_word *> E 3.
Definition bl5_cut_config := left_p 18 {{{ (hxaR,R) }}} bl5_cut_top.

Lemma bl5_cut_quadRect:
  quadRect tm hp_stream bl5_cut_top.
Proof.
  unfold bl5_cut_top.
  eapply downRect_quadRect_concat.
  - exact C16_p_downRect.
  - exact bl5_suffix_quadRect.
Qed.

Lemma bl5_cut_nonhalt:
  ~ halts tm bl5_cut_config.
Proof.
  unfold bl5_cut_config.
  eapply quadRect_nonhalt.
  - exact bl5_cut_quadRect.
  - exact p_stream_realizes.
Qed.

Lemma bl5_init_cut:
  c0 -[tm]->> 58139 / bl5_cut_config.
Proof.
  eapply multistep_c_spec.
  vm_compute; st; reflexivity.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - eapply without_counter; exact bl5_init_cut.
  - exact bl5_cut_nonhalt.
Qed.

End TM1.

Module TM2.

Module Common := TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RB_1LD0RA_0LA0LC_0LD1LF_0LB---").

Definition to_bl5 q :=
  match q with
  | A => D
  | B => A
  | C => B
  | D => C
  | E => E
  | F => F
  end.

Lemma perm : Perm tm Common.tm to_bl5.
Proof.
  split.
  - intros [] [] H; native_compute in H |- *; congruence.
  - intros [] [] s' d q' H; native_compute in H |- *;
      inversion H; reflexivity.
Qed.

Lemma C15_p_period:
  segRLs_n Common.tm
    [Common.signal_head Common.P; Common.signal_head Common.P;
      Common.signal_head Common.P]
    [Common.signal_head Common.Qs; Common.signal_head Common.P]
    (Common.C0 15) (Common.C0 15) 1.
Proof. solve_segRLs_n1_with 100000. Qed.

Lemma qp_heads_two:
  Common.signal_heads Common.qp_stream =
    [Common.signal_head Common.Qs; Common.signal_head Common.P] *>
      Common.signal_heads Common.qp_stream.
Proof.
  rewrite Common.qp_stream_unfold at 1.
  apply Common.signal_heads_cons2.
Qed.

Lemma C15_p_downRect:
  downRect Common.tm Common.hp_stream
    (Common.signal_heads Common.qp_stream) (Common.C0 15) 1.
Proof.
  eapply segRLs_n_inf_trans with
    (P:=fun L R w =>
      L = Common.hp_stream /\
      R = Common.signal_heads Common.qp_stream /\ w = Common.C0 15).
  - intros L R w [-> [-> ->]].
    exists [Common.signal_head Common.P; Common.signal_head Common.P;
      Common.signal_head Common.P],
      [Common.signal_head Common.Qs; Common.signal_head Common.P],
      (Common.C0 15), Common.hp_stream,
      (Common.signal_heads Common.qp_stream).
    split; [cbn; lia|]. split.
    + apply Common.hp_stream_three.
    + split.
      * apply qp_heads_two.
      * split; [apply C15_p_period|repeat split; reflexivity].
  - repeat split; reflexivity.
Qed.

Lemma p_stream_realizes_16:
  leftRealizes Common.tm (A,[0;0]) Common.hp_stream (Common.left_p 16).
Proof.
  eapply leftRealizes_inf_concat with
    (P:=fun h L l =>
      h = (A,[0;0]) /\ L = Common.hp_stream /\ l = Common.left_p 16).
  - intros h L l [-> [-> ->]].
    exists [Common.signal_head Common.P], Common.hp_stream, (A,[0;0]),
      [((D,@nil Sym),(A,[0;0]))], (Common.left_p 16).
    split; [cbn; lia|]. split.
    + apply Common.hp_stream_unfold.
    + split; [reflexivity|]. split.
      * replace 16 with (8*2) by lia. apply Common.left_p_loop.
      * repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.

Lemma edge7_P:
  sideRLs Common.tm [Common.signal_head Common.P]
    (Common.E 7) (Common.C0 6 *> Common.E 3).
Proof.
  unfold Common.E, Common.C0.
  eapply sideRLs_c_spec with (T:=100000).
  - vm_compute; reflexivity.
  - st; reflexivity.
Qed.

Lemma edge7_QQP:
  sideRLs Common.tm
    [Common.signal_head Common.Qs; Common.signal_head Common.Qs;
      Common.signal_head Common.P]
    (Common.E 7) (Common.C0 14 *> Common.E 3).
Proof.
  unfold Common.E, Common.C0.
  eapply sideRLs_c_spec with (T:=100000).
  - vm_compute; reflexivity.
  - st; reflexivity.
Qed.

Lemma signal_heads_cons3 s1 s2 s3 L:
  Common.signal_heads (Cons s1 (Cons s2 (Cons s3 L))) =
    [Common.signal_head s1; Common.signal_head s2; Common.signal_head s3] *>
      Common.signal_heads L.
Proof. repeat rewrite Common.signal_heads_cons. reflexivity. Qed.

Lemma edge7_phase1_quadRect S:
  Common.good 1 S ->
  quadRect Common.tm (Common.signal_heads S) (Common.E 7).
Proof.
  intro HG.
  destruct (Common.good1_inv _ HG) as [[T [-> HT]]|[T [-> HT]]].
  - rewrite Common.signal_heads_cons.
    eapply Common.sideRLs_downRect_quadRect with
      (w:=Common.C0 6) (width:=1%nat)
      (Ledge:=Common.signal_heads (Common.transduce Common.R000 T))
      (top':=Common.E 3).
    + lia.
    + exact edge7_P.
    + change (downRect Common.tm (Common.signal_heads T)
        (Common.signal_heads (Common.transduce Common.R000 T))
        (Common.column Common.R000 2) 1).
      apply Common.column_downRect; exact HT.
    + apply Common.edge_cycle_quadRect.
      exists (Common.transduce Common.R000 T). split.
      * exact (Common.transduce_good Common.R000 T HT).
      * split; reflexivity.
  - destruct (Common.good2_inv _ HT) as [U [-> HU]].
    destruct (Common.good3_inv _ HU) as [V [-> HV]].
    rewrite signal_heads_cons3.
    eapply Common.sideRLs_downRect_quadRect with
      (w:=Common.C0 14) (width:=1%nat)
      (Ledge:=Common.signal_heads (Common.transduce Common.R000 V))
      (top':=Common.E 3).
    + lia.
    + exact edge7_QQP.
    + change (downRect Common.tm (Common.signal_heads V)
        (Common.signal_heads (Common.transduce Common.R000 V))
        (Common.column Common.R000 6) 1).
      apply Common.column_downRect; exact HV.
    + apply Common.edge_cycle_quadRect.
      exists (Common.transduce Common.R000 V). split.
      * exact (Common.transduce_good Common.R000 V HV).
      * split; reflexivity.
Qed.

Definition suffix_word : list Sym :=
  Common.C0 11 ++ Common.C1 8 ++ Common.C0 6 ++
  Common.C0 7 ++ Common.C0 7 ++ Common.C0 8 ++ Common.C0 6 ++
  Common.C1 8 ++ Common.C1 6 ++ Common.C0 7 ++ Common.C0 8 ++
  Common.C0 6 ++ Common.C1 8 ++ Common.C1 6.

Ltac next_column st k Hin Hout :=
  eapply downRect_quadRect_concat;
  [exact (Common.column_downRect st k _ Hin)|];
  pose proof (Common.transduce_good st _ Hin) as Hout;
  cbn [Common.out_phase] in Hout.

Lemma suffix_quadRect:
  quadRect Common.tm (Common.signal_heads Common.qp_stream)
    (suffix_word *> Common.E 7).
Proof.
  unfold suffix_word; repeat rewrite Str_app_assoc.
  pose proof Common.qp_good as H0.
  next_column Common.R021 4 H0 H1.
  next_column Common.R113 3 H1 H2.
  next_column Common.R300 2 H2 H3.
  next_column Common.R021 2 H3 H4.
  next_column Common.R121 2 H4 H5.
  next_column Common.R100 2 H5 H6.
  next_column Common.R000 2 H6 H7.
  next_column Common.R013 2 H7 H8.
  next_column Common.R311 2 H8 H9.
  next_column Common.R121 2 H9 H10.
  next_column Common.R100 2 H10 H11.
  next_column Common.R000 2 H11 H12.
  next_column Common.R013 2 H12 H13.
  next_column Common.R311 2 H13 H14.
  apply edge7_phase1_quadRect; exact H14.
Qed.

Definition cut_top : side := Common.C0 15 *> suffix_word *> Common.E 7.
Definition cut_config :=
  Common.left_p 16 {{{ ((B,[0;0]),R) }}} cut_top.

Lemma old_cut_quadRect:
  quadRect Common.tm Common.hp_stream cut_top.
Proof.
  unfold cut_top.
  eapply downRect_quadRect_concat.
  - exact C15_p_downRect.
  - exact suffix_quadRect.
Qed.

Lemma old_cut_nonhalt:
  ~ halts Common.tm
      (Common.left_p 16 {{{ ((A,[0;0]),R) }}} cut_top).
Proof.
  eapply quadRect_nonhalt.
  - exact old_cut_quadRect.
  - exact p_stream_realizes_16.
Qed.

Lemma cut_nonhalt:
  ~ halts tm cut_config.
Proof.
  eapply perm_nonhalt.
  - exact perm.
  - cbn [cut_config to_bl5] in *.
    exact old_cut_nonhalt.
Qed.

Lemma init_cut:
  c0 -[tm]->> 32572 / cut_config.
Proof.
  eapply multistep_c_spec.
  vm_compute; st; reflexivity.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - eapply without_counter; exact init_cut.
  - exact cut_nonhalt.
Qed.

End TM2.

