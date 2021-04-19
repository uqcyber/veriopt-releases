subsection \<open>Structural Graph Comparison\<close>

theory
  Comparison
imports
  IRGraph
begin

text \<open>
We introduce a form of structural graph comparison that is able to assert structural
equivalence of graphs which differ in zero or more reference node chains for any given nodes.
\<close>

fun find_ref_nodes :: "IRGraph \<Rightarrow> (ID \<rightharpoonup> ID)" where
"find_ref_nodes g = map_of
  (map (\<lambda>n. (n, ir_ref (kind g n))) (filter (\<lambda>id. is_RefNode (kind g id)) (sorted_list_of_set (ids g))))"

fun replace_ref_nodes :: "IRGraph \<Rightarrow> (ID \<rightharpoonup> ID) \<Rightarrow> ID list \<Rightarrow> ID list" where
"replace_ref_nodes g m xs = map (\<lambda>id. (case (m id) of Some other \<Rightarrow> other | None \<Rightarrow> id)) xs"

inductive reachables :: "IRGraph \<Rightarrow> ID list \<Rightarrow> ID set \<Rightarrow> bool" where
"reachables g [] {}" |
"\<lbrakk>node = kind g n;
  new = (inputs_of node) @ (successors_of node);
  reachables g (to_see @ new) seen \<rbrakk> \<Longrightarrow> reachables g (n # to_see) ({n} \<union> seen)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) reachables .

inductive nodeEq :: "(ID \<rightharpoonup> ID) \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> bool" where 
"\<lbrakk> kind g1 n1 = RefNode ref; nodeEq m g1 ref g2 n2 \<rbrakk> \<Longrightarrow> nodeEq m g1 n1 g2 n2" | 
"\<lbrakk> x = kind g1 n1; 
  y = kind g2 n2; 
  is_same_ir_node_type x y;
  replace_ref_nodes g1 m (successors_of x) = successors_of y; 
  replace_ref_nodes g1 m (inputs_of x) = inputs_of y \<rbrakk> 
  \<Longrightarrow> nodeEq m g1 n1 g2 n2"

code_pred [show_modes] nodeEq .

fun diffNodesGraph :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> ID set" where
"diffNodesGraph g1 g2 = (let refNodes = find_ref_nodes g1 in
    { n . n \<in> Predicate.the (reachables_i_i_o g1 [0]) \<and> (case refNodes n of Some _ \<Rightarrow> False | _ \<Rightarrow> True) \<and> \<not>(nodeEq refNodes g1 n g2 n)})"

fun diffNodesInfo :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> (ID \<times> IRNode \<times> IRNode) set" where
"diffNodesInfo g1 g2 = {(nid, kind g1 nid, kind g2 nid) | nid . nid \<in> diffNodesGraph g1 g2}"

fun eqGraph :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
"eqGraph isabelle_graph graal_graph = ((diffNodesGraph isabelle_graph graal_graph) = {})"


end