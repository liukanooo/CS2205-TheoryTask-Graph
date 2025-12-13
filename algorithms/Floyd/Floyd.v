
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope nat.


Section Floyd.

(** Floyd算法用于计算图中所有顶点对之间的最短路径。
    核心思想是通过逐步允许使用更多的顶点作为中间点来优化路径。
    
    循环不变量提示：
    - k-循环不变量：dist[i][j] = shortestPath(i, j, k)
      即 dist[i][j] 是从 i 到 j 只经过前 k 个顶点作为中间点的最短距离
    - i-循环不变量：
      * 对于 i0 < i: dist[i0][j] = shortestPath(i0, j, k)
      * 对于 i0 >= i: dist[i0][j] = shortestPath(i0, j, k-1)
*)

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G)
        {eq_dec: EqDec (V * V) eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).

Record St: Type := mkSt {
  dist: (V * V) -> option Z;
}.

Instance: Settable St := settable! mkSt <dist>.


(** 松弛操作：dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]) *)
Definition update_dist (i j k: V): program St unit :=
  update' (fun s => s <| dist ::= fun dist0 =>
    (i, j) !-> (Z_op_min (dist0 (i, j)) (Z_op_plus (dist0 (i, k)) (dist0 (k, j)))); dist0 |>).

Definition Floyd_j (k: V) (j: V): program St unit :=
  forset (fun v => vvalid g v) (fun i =>
    update_dist i j k).

(** 对于固定的中间点k，遍历所有顶点对(i,j)进行松弛 *)
Definition Floyd_k (k: V): program St unit :=
  forset (fun v => vvalid g v) (Floyd_j k).

(** Floyd主算法：遍历所有可能的中间点k *)
Definition Floyd: program St unit :=
  forset (fun v => vvalid g v) Floyd_k.


(** 
  ===== 循环不变量 ===== 
  Floyd算法的核心不变量：
  在迭代过程中（处理完中间节点集合 done），
  dist[u][v] 存储的是"中间节点仅限于 done 中的顶点"的最短路径。
  
  具体含义：
  - done 表示已经作为"中间节点"处理过的顶点集合
  - dist[u][v] = min { weight(p) | p 是从 u 到 v 的路径，且 p 的中间节点都在 done 中 }
  - 注意：u 和 v 本身不算中间节点，它们是起点和终点
  
  循环不变量的演进：
  - 初始：done = ∅，dist[u][v] 表示不经过任何中间节点的最短路径（即直接边或无穷大）
  - 处理节点 k 后：done = done ∪ {k}，dist[u][v] 更新为
      min(dist[u][v], dist[u][k] + dist[k][v])
    这表示要么不经过 k，要么经过 k 的最短路径
  - 最终：done = 所有顶点，dist[u][v] 表示真正的最短路径
*)

Definition Floyd_loop_invariant (done: V -> Prop) (s: St): Prop :=
  forall u v,
    min_weight_distance_in_vset g u v done (s.(dist) (u, v)).

(** ===== 正确性规范 ===== *)

(** 健全性：如果dist记录了距离n，则n确实是最短距离 *)
Definition distance_soundness (s: St): Prop :=
  forall u v w, s.(dist) (u, v) = w -> min_weight_distance g u v w.

(** 完备性：如果存在最短距离n，则dist正确记录 *)
Definition distance_completeness (s: St): Prop :=
  forall u v w, min_weight_distance g u v w -> s.(dist) (u, v) = w.

Definition distance_correct (s: St): Prop :=
  distance_soundness s /\ distance_completeness s.

(** ===== 主定理 =====
    
    证明 Floyd 算法的正确性：
    如果初始状态满足空集上的循环不变量，
    则算法结束后，dist 数组正确记录了所有点对之间的最短距离。
*)

Definition initialized_state (s: St): Prop := 
  Floyd_loop_invariant ∅ s.

Theorem Floyd_correct: 
  Hoare initialized_state
        Floyd
        (fun _ s => distance_correct s).
Proof.
  unfold Floyd. 
  hoare_cons (Hoare_forset Floyd_loop_invariant).
Admitted.


End Floyd.