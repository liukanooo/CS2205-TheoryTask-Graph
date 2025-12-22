
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
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}. 

Lemma empty_path_edge: forall (g: G) v,
  edge_in_path (empty_path v) = nil. 
Proof.
  intros. 
  pose proof (vpath_iff_epath g (empty_path v) (empty_path_valid g v)) as [Hlen _].
  rewrite empty_path_vertex in Hlen.
  simpl in Hlen.
  assert (length (edge_in_path (empty_path v)) = 0%nat) by lia.
  rewrite length_zero_iff_nil in H. 
  auto.
Qed.

Definition is_path (g: G) (p: P) (u v: V): Prop :=
  path_valid g p /\ head p = u /\ tail p = v.

Definition is_empty_path (p: P): Prop :=
  exists v, p = empty_path v.

Definition interior (l: list V): list V := removelast (tl l).

(* 路径的中间节点只能经过vset中的顶点 *)
Definition is_path_through_vset 
  (g: G) (p: P) (u v: V) 
  (vset: V -> Prop): Prop :=
  is_path g p u v /\ (forall v, In v (interior (vertex_in_path p)) -> v ∈ vset).

(* 路径的事实上的中间节点可以直接用interior函数得到 *)

(* 所有的路径顶点集合都不为空 *)
Lemma path_valid_vertex_not_nil: forall g p,
  path_valid g p ->
  vertex_in_path p <> nil.
Proof.
  intros.
  pose proof vpath_iff_epath g p H. 
  destruct H0 as [contra _]. 
  unfold not; intros; rewrite H0 in contra. 
  simpl in contra. 
  lia.
Qed.

Definition is_simple_path (g: G) (p: P) (u v: V): Prop :=
  is_path g p u v /\ NoDup (vertex_in_path p). 

Lemma path_simplfier: forall g p u v,
  is_path g p u v ->
  exists q, is_simple_path g q u v.
Proof.
  intros.
  destruct H as [Hpath Hnodup].
  unfold is_simple_path. 
Admitted.



End path.