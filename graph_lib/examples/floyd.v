
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From ListLib Require Import Base.Positional.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.

Import SetsNotation.
Local Open Scope sets.


Section floyd.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G).

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).

(** ===== Floyd 算法证明路线 =====  *)


(** ===== 路径基本性质引理 ===== *)

(** 引理1：路径拼接保持路径 *)
Lemma path_concat_valid: 
  forall (i j k: V) (p1 p2: P), 
    is_path g p1 i j -> 
    is_path g p2 j k -> 
    is_path g (concat_path p1 p2) i k.
Proof. 
  intros. 
  unfold is_path in *. 
  destruct H as [Hvalid1 [Hhead1 Htail1]].
  destruct H0 as [Hvalid2 [Hhead2 Htail2]]. 
  assert (Hvalid: path_valid g (concat_path p1 p2)) 
  by (apply concat_path_valid; subst; auto).
  split; [|split]; auto. 
  - apply Some_inversion. 
    erewrite (head_valid g); eauto. 
    rewrite concat_path_vertex. 
    pose proof path_valid_vertex_not_nil g p1 Hvalid1. 
    destruct (vertex_in_path p1) eqn:Heq; [congruence|clear H]. 
    rewrite <- app_comm_cons. 
    rewrite hd_error_cons. 
    apply Some_injection in Hhead1. 
    erewrite head_valid in Hhead1; eauto. 
    rewrite Heq in Hhead1. 
    rewrite hd_error_cons in Hhead1. 
    rewrite Hhead1. 
    reflexivity.
  - apply Some_inversion. 
    erewrite (tail_valid g); eauto. 
    rewrite concat_path_vertex. 
    rewrite <- Htail2. 
    erewrite tail_valid; eauto. 
    apply tl_error_app_skipn_connected. 
    eapply path_valid_vertex_not_nil; eauto. 
    eapply path_valid_vertex_not_nil; eauto. 
    apply Some_injection in Htail1, Hhead2. 
    erewrite head_valid in Hhead2; eauto. 
    erewrite tail_valid in Htail1; eauto. 
    rewrite Htail1, Hhead2. 
    reflexivity.  
Qed.

(** 引理2：路径拼接的权重等于两段路径权重之和 *)
Lemma path_concat_weight: 
  forall (p1 p2: P),
    path_valid g p1 ->
    path_valid g p2 ->
    tail p1 = head p2 ->
    path_weight g (concat_path p1 p2) = Z_op_plus (path_weight g p1) (path_weight g p2).
Proof.
  intros.
  unfold path_weight. 
  rewrite concat_path_edge.
  rewrite map_app.
  rewrite Zlist_sum_app.
  reflexivity.
Qed.

(** 引理3: 通过 vset 的路径，可以扩展到通过 vset ∪ {k} 的路径集合 *)
Lemma path_vset_mono: forall (u v k: V) (p: P) (vset: V -> Prop),
  is_path_through_vset g p u v vset ->
  is_path_through_vset g p u v (vset ∪ [k]).
Proof.
  intros.
  unfold is_path_through_vset in *.
  destruct H as [Hpath Hvset].
  split; [auto|intros].
  apply Hvset in H. 
  left; auto. 
Qed.


(** *引理4: 最短路径都是简单路径 *) 
Lemma min_weight_path_simple: forall (u v: V) (p: P),
  min_weight_path g u v p ->
  is_simple_path g p u v.
Proof.
Admitted.

(* 定理1前置: 如果一条只经过 vset U {k} 的路径 p 经过了 k，
    那么它可以分解为两段只经过 vset 的路径 *)
(* 它和定理1可以通过path_simplfier互推 *)
Lemma path_decompose_at_vertex: forall (u v k: V) (p: P) (vset: V -> Prop),
  is_path_through_vset g p u v (vset ∪ [k]) ->
  In k (vertex_in_path p) ->           
  exists p1 p2,
    is_path_through_vset g p1 u k vset /\
    is_path_through_vset g p2 k v vset.
Proof.
Admitted.


(** 定理1: 如果一条只经过 vset U {k} 的简单路径 p 经过了 k，
    那么它可以恰好分解为两段只经过 vset 的路径,使得路径权重和相等 *)
Lemma path_decompose_simple: forall (u v k: V) (p: P) (vset: V -> Prop),
  is_simple_path g p u v ->
  is_path_through_vset g p u v (vset ∪ [k]) ->
  In k (vertex_in_path p) ->           
  exists p1 p2,
    is_path_through_vset g p1 u k vset /\
    is_path_through_vset g p2 k v vset /\
    path_weight g p = Z_op_plus (path_weight g p1) (path_weight g p2).
Admitted.

(* 定理2: 两段经过 S 的中间顶点为 k 的路径拼接起来，是一段经过 S ∪ {k} 的路径。 *)
Lemma path_concat_vset_inclusion: 
  forall (u v k: V) (p1 p2: P) (vset: V -> Prop),
    is_path_through_vset g p1 u k vset ->
    is_path_through_vset g p2 k v vset ->
    is_path_through_vset g (concat_path p1 p2) u v (vset ∪ [k]).
Proof.
Admitted.

(** ===== 最短路径基本性质引理 ===== *)

(** 引理5: 路径集合单调性蕴含最短距离单调性 *)
Lemma min_distance_vset_mono: forall u v k vset w1 w2,
  min_weight_distance_in_vset g u v vset w1 ->
  min_weight_distance_in_vset g u v (vset ∪ [k]) w2 ->
  Z_op_le w2 w1.
Admitted.


(** ===== 松弛操作的正确性引理 ===== *)


(** 目标: 证明Floyd算法中松弛操作的正确性 *)
Lemma floyd_relaxation_correct: 
  forall (i j k: V) (vset: V -> Prop) (w_ik w_kj w_ij: option Z),
    min_weight_distance_in_vset g i k vset w_ik -> 
    min_weight_distance_in_vset g k j vset w_kj -> 
    min_weight_distance_in_vset g i j vset w_ij ->
    min_weight_distance_in_vset g i j (vset ∪ [k]) (Z_op_min w_ij (Z_op_plus w_ik w_kj)).
Admitted.


End floyd.
