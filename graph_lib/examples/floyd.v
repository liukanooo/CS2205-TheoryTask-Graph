
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
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

(** ===== Floyd 算法证明路线 =====

*)
Lemma path_through_empty_is_direct: forall u v p,
  is_path_through_vset g p u v ∅ ->
  exists e, step_aux g e u v.
Admitted.


(** ===== 路径基本性质引理 ===== *)

(** 路径拼接保持路径性质 *)
Lemma path_concat_valid: forall (i j k: V) (p1 p2: P), 
  is_path g p1 i j -> 
  is_path g p2 j k -> 
  is_path g (concat_path p1 p2) i k.
Admitted.

(** 路径拼接的权重等于两段路径权重之和 *)
Lemma path_concat_weight: forall (i j k: V) (p1 p2: P),
  path_valid g p1 ->
  path_valid g p2 ->
  tail p1 = head p2 ->
  path_weight g (concat_path p1 p2) = Z_op_plus (path_weight g p1) (path_weight g p2).
Admitted.

(** 如果一条路径经过顶点 k，那么可以分解为两段 *)
Lemma path_decompose_at_vertex: forall (u v k: V) (p: P) (vset: V -> Prop),
  is_path_through_vset g p u v (vset ∪ [k]) ->
  In k (vertex_in_path p) ->
  (* 则存在两段路径，分别从 u 到 k 和从 k 到 v *)
  exists p1 p2,
    is_path_through_vset g p1 u k vset /\
    is_path_through_vset g p2 k v vset /\
    Z_op_le (path_weight g p) (Z_op_plus (path_weight g p1) (path_weight g p2)).
Admitted.

(** 通过 vset 的路径，可以扩展到通过 vset ∪ {k} 的路径集合 *)
Lemma path_vset_mono: forall (u v k: V) (p: P) (vset: V -> Prop),
  is_path_through_vset g p u v vset ->
  is_path_through_vset g p u v (vset ∪ [k]).
Admitted.

(** ===== 最短路径基本性质引理 ===== *)

(** 路径集合单调性蕴含最短距离单调性 *)
Lemma min_distance_vset_mono: forall u v k vset w1 w2,
  min_weight_distance_in_vset g u v vset w1 ->
  min_weight_distance_in_vset g u v (vset ∪ [k]) w2 ->
  Z_op_le w2 w1.
Admitted.


(** ===== 松弛操作的正确性引理 ===== *)

Lemma floyd_relaxation_correct: 
  forall (i j k: V) (vset: V -> Prop) (w_ik w_kj w_ij: option Z),
    min_weight_distance_in_vset g i k vset w_ik -> 
    min_weight_distance_in_vset g k j vset w_kj -> 
    min_weight_distance_in_vset g i j vset w_ij ->
    min_weight_distance_in_vset g i j (vset ∪ [k]) (Z_op_min w_ij (Z_op_plus w_ik w_kj)).
Admitted.


End floyd.
