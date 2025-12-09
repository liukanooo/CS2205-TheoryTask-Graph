Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.Syntax.
Require Import SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Lia.
Local Open Scope list.

Import ListNotations.
Import SetsNotation.
Local Open Scope sets.

(** * 树的基本定义 *)

Class Tree (G V E: Type) {pg: Graph G V E} {gv: GValid G} (A: Type) {path: Path G V E A}:=
{
  tree_connected: forall g, gvalid g -> connected g;
  tree_no_curcuit: forall g, gvalid g -> ~ have_simple_circuit g;
}.

(** * 最小生成树相关定义 *)
Section MST_DEFINITIONS.

Context {V E: Type}.

(** 边集的总权重 *)
Fixpoint edges_total_weight 
  (weight: E -> option nat) (edges: list E): nat :=
  match edges with
  | nil => 0
  | e :: es => 
      match weight e with
      | Some w => w + edges_total_weight weight es
      | None => edges_total_weight weight es
      end
  end.

(** 跨边（Cut Edge）定义：一端在集合内，一端在集合外 *)
Definition is_cut_edge {G: Type} {pg: Graph G V E}
  (g: G) (vset: V -> Prop) (e: E): Prop :=
  exists u v, step_aux g e u v /\ u ∈ vset /\ ~ v ∈ vset.

(** 边集构成的子图中两点连通 *)
Inductive connected_by_edge_list {G: Type} {pg: Graph G V E}
  (g: G) (edges: list E): V -> V -> Prop :=
  | conn_refl: forall v, connected_by_edge_list g edges v v
  | conn_step: forall u v w e,
      In e edges ->
      step_aux g e u v ->
      connected_by_edge_list g edges v w ->
      connected_by_edge_list g edges u w.

(** 边集无环 *)
Definition edge_list_acyclic {G: Type} {pg: Graph G V E} 
  {eq_dec_E: forall (e1 e2: E), {e1 = e2} + {e1 <> e2}}
  (g: G) (edges: list E): Prop :=
  forall e u v, 
    In e edges -> 
    step_aux g e u v ->
    ~ connected_by_edge_list g (remove eq_dec_E e edges) u v.

(** 边集连接给定顶点集 *)
Definition edge_list_spans {G: Type} {pg: Graph G V E}
  (g: G) (edges: list E) (vertices: V -> Prop): Prop :=
  forall u v, u ∈ vertices -> v ∈ vertices -> 
    connected_by_edge_list g edges u v.

(** 边集是某个顶点集上的生成树 *)
Definition is_spanning_tree_of {G: Type} {pg: Graph G V E}
  {eq_dec_E: forall (e1 e2: E), {e1 = e2} + {e1 <> e2}}
  (g: G) (edges: list E) (vertices: V -> Prop): Prop :=
  @edge_list_acyclic G pg eq_dec_E g edges /\
  @edge_list_spans G pg g edges vertices.

(** 边集是某个顶点集上的最小生成树 *)
Definition is_mst_of {G: Type} {pg: Graph G V E}
  {eq_dec_E: forall (e1 e2: E), {e1 = e2} + {e1 <> e2}}
  (g: G) (edges: list E) (vertices: V -> Prop) 
  (weight: E -> option nat): Prop :=
  @is_spanning_tree_of G pg eq_dec_E g edges vertices /\
  (forall edges',
    @is_spanning_tree_of G pg eq_dec_E g edges' vertices ->
    edges_total_weight weight edges <= edges_total_weight weight edges').

(** 子图关系（边集包含） *)
Definition edge_list_subgraph (edges1 edges2: list E): Prop :=
  forall e, In e edges1 -> In e edges2.

(** 边集可扩展为最小生成树 *)
Definition extendable_to_mst_of {G: Type} {pg: Graph G V E}
  {eq_dec_E: forall (e1 e2: E), {e1 = e2} + {e1 <> e2}}
  (g: G) (edges: list E) (vertices: V -> Prop) 
  (weight: E -> option nat): Prop :=
  exists full_edges,
    edge_list_subgraph edges full_edges /\
    @is_mst_of G pg eq_dec_E g full_edges vertices weight.

End MST_DEFINITIONS.

Section TREE.
Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {A: Type}
        {path: Path G V E A}
        {emptypath: EmptyPath G V E A path}
        {singlepath: SinglePath G V E A path}
        {concatpath: ConcatPath G V E A path}
        {tree: @Tree G V E pg gv A path}
        {g: G}
        {gvalid: gvalid g}.

Lemma tree_have_path: 
  forall u v,
  vvalid g u ->
  vvalid g v ->
  exists p, valid_epath g u p v.
Proof.
  intros.
  pose proof (tree_connected g gvalid u v H H0).
  unfold reachable in H1; induction_1n H1.
  * exists nil; unfold valid_epath. 
    exists (empty_path v). (split;[|split;[|split]]).
    - apply empty_path_valid.
    - assert (length (edge_in_path (empty_path v)) = 0). {
        pose proof vpath_iff_epath g (empty_path v) (empty_path_valid g v) as [Hl _].
        rewrite empty_path_vertex in Hl; simpl in Hl. 
        lia.
      }
      destruct (edge_in_path (empty_path v)) eqn: Hle; auto. 
      inversion H1.
    - rewrite empty_path_vertex. simpl. auto.
    - rewrite empty_path_vertex. simpl. auto.
  * apply step_vvalid in H2 as ?; destruct H3 as [_ Hu0].
    apply IHrt in H0 as Hp; auto.
    destruct Hp as [p].
    destruct H2 as [e].
    destruct H3 as [p0 [? [? []]]].
    exists (e :: p).
    exists (concat_path (single_path u u0 e) p0). 
    (split;[|split;[|split]]).
    - apply concat_path_valid; auto. 
      apply single_path_valid; auto. 
      assert (Some (path.tail (single_path u u0 e)) = Some (path.head p0)). 
      2: { inversion H7; subst; reflexivity. }
      erewrite head_valid; eauto. 
      erewrite tail_valid. 
      2: { apply single_path_valid; eauto. }
      unfold tl_error. 
      rewrite single_path_vertex; simpl. 
      rewrite H5; auto. 
    - pose proof concat_path_edge (single_path u u0 e) p0 as He; rewrite He. 
      rewrite single_path_edge. rewrite H4. simpl. auto.
    - pose proof concat_path_vertex (single_path u u0 e) p0 as He; rewrite He. 
      rewrite single_path_vertex. simpl. auto.
    - pose proof concat_path_vertex (single_path u u0 e) p0 as He; rewrite He. 
      rewrite single_path_vertex. 
      destruct ((vertex_in_path p0)) eqn: Heqn; simpl.
      { inversion H5. }
      { simpl in H6. destruct (length l) eqn: Hl; simpl in *; auto. 
        inversion H5; inversion H6; subst; reflexivity. }
Qed.

Lemma tree_have_simple_path: 
  forall u v,
  vvalid g u ->
  vvalid g v ->
  exists p, simple_epath g u p v.
Proof.
  intros.
  pose proof (tree_have_path u v H H0) as [p Hp].
  eapply path_simplfier; eauto. 
Qed.


Lemma tree_add_edge_have_simple_circuit: 
  forall g' u v e,
  addEdgeUndirected g g' u v e ->
  exists w p, simple_circuit g' p w.
Proof.
  intros.
  pose proof H as H'.
  destruct H.
  destruct addEdge_undirected_premise as [H [H0 H1]].
  pose proof (tree_have_simple_path u v H H0) as [p Hp].
  exists v, (e :: p).
  split; auto.
  - apply NoDup_cons; auto.
    * unfold not; intros.
      destruct Hp.
      eapply valid_path_evalid in H2; eauto.
    * apply Hp.
  - destruct Hp as [? [p0 [? [? []]]]]. 
    exists (concat_path (single_path v u e) p0). 
    (split;[|split;[|split]]).
Admitted.

End TREE.

(** * 最小生成树的静态性质 - 供 Prim 和 Kruskal 算法共用 *)
Section MST_PROPERTIES.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {eq_dec_E: forall (e1 e2: E), {e1 = e2} + {e1 <> e2}}
        {A: Type}
        {path: Path G V E A}
        {emptypath: EmptyPath G V E A path}
        {singlepath: SinglePath G V E A path}
        {concatpath: ConcatPath G V E A path}
        (g: G)
        (gvalid_g: gvalid g)
        (weight: E -> option nat).

(** 性质1：路径简化 - 如果两点间存在路径，则存在简单路径 *)
Lemma path_simplifier: forall u v p,
  valid_epath g u p v ->
  exists q, simple_epath g u q v.
Proof.
  intros.
  eapply path_simplfier; eauto.
Qed.

(** 性质2：树中任意两点存在路径 *)
Lemma tree_edges_have_path: forall (edges: list E) (vertices: V -> Prop) u v,
  @is_spanning_tree_of V E G pg eq_dec_E g edges vertices ->
  u ∈ vertices -> v ∈ vertices ->
  connected_by_edge_list g edges u v.
Proof.
  intros.
  destruct H as [_ Hspans].
  apply Hspans; auto.
Qed.

(** 性质3：树中任意两点存在唯一简单路径 *)
Lemma tree_have_unique_simple_path: forall (edges: list E) (vertices: V -> Prop) u v p1 p2,
  @is_spanning_tree_of V E G pg eq_dec_E g edges vertices ->
  u ∈ vertices -> v ∈ vertices ->
  simple_epath g u p1 v ->
  simple_epath g u p2 v ->
  (forall e, In e p1 -> In e edges) ->
  (forall e, In e p2 -> In e edges) ->
  p1 = p2.
Admitted.

(** 性质4：往树中加边形成唯一简单回路 *)
Lemma tree_add_edge_have_circuit: forall (edges: list E) (vertices: V -> Prop) e u v,
  @is_spanning_tree_of V E G pg eq_dec_E g edges vertices ->
  step_aux g e u v ->
  u ∈ vertices -> v ∈ vertices ->
  ~ In e edges ->
  exists c, simple_circuit g (e :: c) u /\ 
            (forall e', In e' c -> In e' edges).
Admitted.

(** 性质5：简单回路上若存在跨边，则存在另一条跨边（Prim算法关键引理） *)
Lemma circuit_crossing_cut_has_two_edges: forall (circuit: list E) (vset: V -> Prop) u e,
  simple_circuit g circuit u ->
  In e circuit ->
  is_cut_edge g vset e ->
  exists f, In f circuit /\ f <> e /\ is_cut_edge g vset f.
Admitted.

(** 性质6：从连通图中移除环路上的边，连通性不变 *)
Lemma remove_edge_on_circuit_preserves_connectivity: 
  forall (edges: list E) (circuit: list E) e u,
  (forall e', In e' circuit -> In e' edges) ->
  simple_circuit g circuit u ->
  In e circuit ->
  forall x y, connected_by_edge_list g edges x y ->
              connected_by_edge_list g (remove eq_dec_E e edges) x y.
Admitted.

(** 性质7：往树中加边再删去环路中任意边，仍是树 *)
Lemma tree_add_edge_delete_on_circuit_is_tree: 
  forall (edges: list E) (vertices: V -> Prop) e f u v circuit,
  @is_spanning_tree_of V E G pg eq_dec_E g edges vertices ->
  step_aux g e u v ->
  u ∈ vertices -> v ∈ vertices ->
  ~ In e edges ->
  simple_circuit g (e :: circuit) u ->
  In f circuit ->
  @is_spanning_tree_of V E G pg eq_dec_E g (remove eq_dec_E f (e :: edges)) vertices.
Admitted.

(** 性质8：加入边再删除权重更大的边，总权重减小 *)
Lemma list_sum_add_edge: forall (edges: list E) e f,
  In f edges ->
  (exists we wf, weight e = Some we /\ weight f = Some wf /\ we <= wf) ->
  edges_total_weight weight (e :: remove eq_dec_E f edges) <= 
  edges_total_weight weight edges.
Admitted.

(** 性质9：空边集可扩展为MST（Kruskal初始条件） *)
Lemma empty_extendable_to_mst: forall (vertices: V -> Prop),
  connected g ->
  (forall v, v ∈ vertices -> vvalid g v) ->
  @extendable_to_mst_of V E G pg eq_dec_E g nil vertices weight.
Admitted.

(** 性质10：切边引理 - 最小权重跨边是安全边（Prim算法核心引理） *)
Lemma min_cut_edge_is_safe: forall (edges: list E) (vertices: V -> Prop) e,
  @extendable_to_mst_of V E G pg eq_dec_E g edges vertices weight ->
  is_cut_edge g vertices e ->
  (forall e', is_cut_edge g vertices e' -> 
    exists we we', weight e = Some we /\ weight e' = Some we' /\ we <= we') ->
  @extendable_to_mst_of V E G pg eq_dec_E g (e :: edges) (vertices ∪ (fun v => exists u, step_aux g e u v /\ ~ v ∈ vertices)) weight.
Admitted.

(** 性质11：不形成环的最小权重边是安全边（Kruskal算法核心引理） *)
Lemma min_non_cycle_edge_is_safe: forall (edges: list E) (vertices: V -> Prop) e u v,
  @extendable_to_mst_of V E G pg eq_dec_E g edges vertices weight ->
  step_aux g e u v ->
  ~ connected_by_edge_list g edges u v ->
  (forall e' u' v', 
    step_aux g e' u' v' -> 
    ~ connected_by_edge_list g edges u' v' ->
    exists we we', weight e = Some we /\ weight e' = Some we' /\ we <= we') ->
  @extendable_to_mst_of V E G pg eq_dec_E g (e :: edges) vertices weight.
Admitted.

End MST_PROPERTIES.

