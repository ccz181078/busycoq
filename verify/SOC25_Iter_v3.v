From BusyCoq Require Import Helper TM Individual62 BinaryCounter_v2 SimplTape ES_v2 Eqv_WordPairs SOC25_Iter Eqv_v3.
Require Import Lia PeanoNat List. Import ListNotations.
Close Scope sym. Open Scope nat_scope.

(* The two SOC25 machines that ccz's Eqv_v3.v proves halting-equivalent to
   TM90.tm / TM97.tm (TM187 and TM135). Names that Eqv_v3 shadows (f, Config,
   C, cfg0) are qualified. *)

Module TM187_iter.
Lemma eqv_model : halts TM187.tm c0 <-> iter_halts SOC25Iter.f (SOC25Model.cfgL 1 1 1).
Proof.
  rewrite TM187.eqv.
  change TM187.tm' with TM90.tm.
  exact (TM90_iter.eqv_model false).
Qed.
Lemma eqv_F : halts TM187.tm c0 <-> iter_halts SOC25Iter.F (1, 2).
Proof.
  rewrite TM187.eqv.
  change TM187.tm' with TM90.tm.
  exact (TM90_iter.eqv_F false).
Qed.
End TM187_iter.

Module TM135_iter.
Lemma eqv_model : halts TM135.tm c0 <-> iter_halts SOC25Iter.f (SOC25Model.cfgL 1 1 2).
Proof.
  rewrite TM135.eqv.
  change TM135.tm' with (TM97.machine false).
  exact (TM97_iter.eqv_model false).
Qed.
Lemma eqv_F : halts TM135.tm c0 <-> iter_halts SOC25Iter.F (1, 3).
Proof.
  rewrite TM135.eqv.
  change TM135.tm' with (TM97.machine false).
  exact (TM97_iter.eqv_F false).
Qed.
End TM135_iter.

Print Assumptions TM187_iter.eqv_model.
Print Assumptions TM187_iter.eqv_F.
Print Assumptions TM135_iter.eqv_model.
Print Assumptions TM135_iter.eqv_F.
