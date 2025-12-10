
Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Arith.Arith.
From GraphLib Require Import graph_basic reachable_basic Syntax path.

Import ListNotations.
Import SetsNotation.

Local Open Scope sets.
Local Open Scope list.

Section path.
  
Context {G V E: Type}
        {P: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {path: Path G V E P}
        {singlepath: SinglePath G V E P path}. 

Definition is_path (g: G) (p: P) (u v: V): Prop :=
  path_valid g p /\ head p = u /\ tail p = v.

Definition is_path_through_vset (g: G) (p: P) (u v: V) (vset: V -> Prop): Prop :=
  is_path g p u v /\ 
    forall w, In w (vertex_in_path p) -> vset w \/ w = u \/ w = v.

Lemma through_empty_vset: forall g u v e,
  step_aux g e u v <->
  is_path_through_vset g (single_path u v e) u v ∅.
Proof.
  intros; split; intros. 
  - split. 
    * split; [|split]. 
      ** apply single_path_valid; auto.
      ** admit. 
      ** admit. 
    * intros. 
      rewrite single_path_vertex in H0. 
      destruct H0; subst. 
      tauto. admit. 
Admitted.

End path.