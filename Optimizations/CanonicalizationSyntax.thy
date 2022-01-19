theory CanonicalizationSyntax
imports CanonicalizationTreeProofs HOL.Ctr_Sugar OptimizationDSL.Markup
keywords
  "phase" :: thy_decl and 
  "trm" :: quasi_command and
  "optimization" :: thy_goal_defn and
  "print_optimizations" :: diag
begin


fun size :: "IRExpr \<Rightarrow> nat" where
  "size (UnaryExpr op e) = (size e) + 1" |
  "size (BinaryExpr BinAdd x y) = (size x) + ((size y) * 2)" |
  "size (BinaryExpr op x y) = (size x) + (size y)" |
  "size (ConditionalExpr cond t f) = (size cond) + (size t) + (size f) + 2" |
  "size (ConstantExpr c) = 1" |
  "size (ParameterExpr ind s) = 2" |
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 2" |
  "size (VariableExpr x s) = 2"

lemma size_gt_0: "size e > 0"
proof (induction e)
case (UnaryExpr x1 e)
  then show ?case by auto
next
case (BinaryExpr x1 e1 e2)
then show ?case by (cases x1; auto)
next
  case (ConditionalExpr e1 e2 e3)
  then show ?case by auto
next
  case (ParameterExpr x1 x2)
then show ?case by auto
next
  case (LeafExpr x1 x2)
  then show ?case by auto
next
  case (ConstantExpr x)
  then show ?case by auto
next
  case (ConstantVar x)
  then show ?case by auto
next
  case (VariableExpr x1 x2)
  then show ?case by auto
qed

lemma binary_expr_size_gte_2: "size (BinaryExpr op x y) \<ge> 2"
  apply (induction "BinaryExpr op x y") apply auto apply (cases op; auto) using size_gt_0
  apply (metis One_nat_def Suc_leI add_le_mono mult_2_right numeral_Bit0 numeral_code(1) trans_le_add2)
  by (metis Suc_leI add_2_eq_Suc' add_Suc_shift add_mono numeral_2_eq_2 size_gt_0)+

lemma "size e = 1 = is_ConstantExpr e"
  apply (cases e; auto) using size_gt_0
  apply (metis) using size_gt_0
  by (metis binary_expr_size_gte_2 lessI not_less numeral_2_eq_2)

lemma nonconstants_gt_one: "\<not> (is_ConstantExpr e) \<Longrightarrow> size e > 1"
  apply (cases e; auto) using size_gt_0
  apply simp using size_gt_0
  using Suc_le_eq binary_expr_size_gte_2 numeral_2_eq_2 by auto

lemma size_det: "x = y \<Longrightarrow> size x = size y"
  by auto

fun rewrite_obligation :: "IRExpr Rewrite \<Rightarrow> bool" where
  "rewrite_obligation (Transform x y) = (y \<le> x)" |
  "rewrite_obligation (Conditional x y cond) = (cond \<longrightarrow> (y \<le> x))" |
  "rewrite_obligation (Sequential x y) = (rewrite_obligation x \<and> rewrite_obligation y)" |
  "rewrite_obligation (Transitive x) = rewrite_obligation x"

value "exp[abs e]"
ML_val \<open>@{term "abs e"}\<close>
ML_val \<open>@{term "x & x"}\<close>
ML_val \<open>@{term "cond ? tv : fv"}\<close>
ML_val \<open>@{term "x < y"}\<close>
ML_val \<open>@{term "c < y"}\<close>
ML_val \<open>@{term "a \<Longrightarrow> c < y"}\<close>
ML_val \<open>@{term "x << y"}\<close>

value "exp[c1 + y]"

datatype Type =
  Integer |
  Float |
  Object |
  Unknown

definition type :: "IRExpr \<Rightarrow> Type" where
  "type e = (case (stamp_expr e) of
    IntegerStamp _ _ _ \<Rightarrow> Integer
    | ObjectStamp _ _ _ _ \<Rightarrow> Object
    | _ \<Rightarrow> Unknown)"

lemma unfold_type[simp]:
  "(type x = Integer) = is_IntegerStamp (stamp_expr x)"
  unfolding type_def using is_IntegerStamp_def
  using Stamp.case_eq_if Stamp.disc(1) Type.distinct(1) Type.distinct(3)
  by (simp add: Stamp.case_eq_if)

definition type_safe :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "type_safe e1 e2 = 
    ((type e1 = type e2) 
    \<and> (is_IntegerStamp (stamp_expr e1) 
        \<longrightarrow> (stp_bits (stamp_expr e1) = stp_bits (stamp_expr e2))))"

fun int_and_equal_bits :: "Value \<Rightarrow> Value \<Rightarrow> bool" where
  "int_and_equal_bits (IntVal32 e1) (IntVal32 e2) = True" |
  "int_and_equal_bits (IntVal64 e1) (IntVal64 e2) = True" |
  "int_and_equal_bits _ _ = False"

lemma unfold_int_typesafe[simp]:
  assumes "type e1 = Integer"
  shows "type_safe e1 e2 = 
    ((type e1 = type e2) \<and>
    (stp_bits (stamp_expr e1) = stp_bits (stamp_expr e2)))"
proof -
  have "is_IntegerStamp (stamp_expr e1)"
    using assms unfold_type by simp
  then show ?thesis unfolding type_safe_def
    by simp
qed

experiment begin
lemma add_intstamp_prop:
  assumes "type x = Integer"
  assumes "type_safe x y"
  shows "type exp[x + y] = Integer"
  using assms unfolding type_def type_safe_def
  using stamp_expr.simps(3) stamp_binary.simps(1)
  using is_IntegerStamp_def type_def unfold_type sorry

lemma sub_intstamp_prop:
  assumes "type x = Integer"
  assumes "type_safe x y"
  shows "type exp[x - y] = Integer"
  using assms unfolding type_def type_safe_def
  using stamp_expr.simps(3) stamp_binary.simps(1) sorry
end

lemma uminus_intstamp_prop:
  assumes "type x = Integer"
  shows "type exp[-x] = Integer"
  using assms unfolding type_def type_safe_def
  using stamp_expr.simps(1) stamp_unary.simps(1)
  by (metis Stamp.collapse(1) Stamp.discI(1) type_def unfold_type unrestricted_stamp.simps(2))


lemma assume_proof :
  assumes "type x = Integer"
  assumes "type_safe x y"
  shows "rewrite_obligation ((x + (-y) \<mapsto> x - y))"
  unfolding rewrite_obligation.simps 
  unfolding le_expr_def apply (rule allI)+ apply (rule impI)
  using assms unfolding type_def type_safe_def 
  using CanonicalizeAddProof CanonicalizeAdd.intros
  sorry
(*
proof (induction rule: evaltree.induct)
  fix m p
  have "is_IntegerStamp (stamp_expr ?lhs)"
    using assms unfolding type_def
    by (smt (z3) Stamp.collapse(1) Stamp.sel(1) add_intstamp_prop assms(1) stamp_expr.simps(1) stamp_unary.simps(1) uminus_intstamp_prop unfold_int_typesafe unfold_type unrestricted_stamp.simps(2))
  obtain v where lhs: "[m,p] \<turnstile> ?lhs \<mapsto> v"
    using BinaryExprE evalDet sorry
  obtain v2 where rhs: "[m,p] \<turnstile> ?rhs \<mapsto> v2"
    sorry
  then show "v = v2"
    sorry
  then show ?thesis
*)


lemma "rewrite_obligation ((x + (-y)) \<mapsto> (x - y) when (type x = Integer \<and> type_safe x y))"
  sorry


lemma "(size exp[x + (-y)]) > (size exp[x - y])"
  using size.simps(1,2)
  by force


datatype RewriteResult =
  success IRExpr |
  fail

ML \<open>
datatype 'a Rewrite =
  Transform of 'a * 'a |
  Conditional of 'a * 'a * term |
  Sequential of 'a Rewrite * 'a Rewrite |
  Transitive of 'a Rewrite

type rewrite =
  {name: string, rewrite: term Rewrite}

type phase =
  {name: string, rewrites: rewrite list, preconditions: term list}

type phase_store = (string list * (string -> phase option))

datatype phase_state =
  NoPhase of phase_store |
  InPhase of (string * phase_store * term)

signature PhaseState =
sig
  val get: theory -> phase_state
  val add: rewrite -> theory -> theory
  val reset: theory -> theory
  val enter_phase: string -> term -> theory -> theory
  val exit_phase: theory -> theory
end;

structure RWList: PhaseState =
struct

val empty = NoPhase ([], (fn _ => NONE));

fun merge_maps (left: 'a list * ('a -> 'b option)) (right: 'a list * ('a -> 'b option)) =
  ((fst left) @ (fst right), fn x => (case (snd left) x of
    NONE => (snd right) x |
    SOME v => SOME v))

structure RewriteStore = Theory_Data
(
  type T = phase_state;
  val empty = empty;
  val extend = I;
  fun merge (lhs, rhs) = 
    case lhs of
      NoPhase left_store => (case rhs of
        NoPhase right_store => NoPhase (merge_maps left_store right_store) |
        InPhase (name, right_store, trm) => InPhase (name, (merge_maps left_store right_store), trm)) |
      InPhase (name, left_store, trm) => (case rhs of
        NoPhase right_store => InPhase (name, (merge_maps left_store right_store), trm) |
        InPhase (name, right_store, trm) => InPhase (name, (merge_maps left_store right_store), trm))
);

val get = RewriteStore.get;

fun expand_phase rewrite (phase: phase) =
  {name = (#name phase), rewrites = cons rewrite (#rewrites phase), preconditions = (#preconditions phase)}

fun update_existing name (dom, map) trm rewrite =
  let
    val value = map name
  in
    case value of
      NONE => raise TERM ("phase not in store", []) |
      SOME v => InPhase (name, (dom, (fn id => (if id = name then SOME (expand_phase rewrite v) else map id))), trm)
  end

fun add t thy = RewriteStore.map (fn state =>
  case state of
    NoPhase _ => raise TERM ("Optimization phase missing", []) |
    InPhase (name, store, trm) => update_existing name store trm t
  ) thy

val reset = RewriteStore.put empty;

fun new_phase name = {name = name, rewrites = ([] : rewrite list), preconditions = ([] : term list)};

fun enter_phase name trm thy = RewriteStore.map (fn state =>
  case state of
    NoPhase (dom, store) => InPhase (name, ([name] @ dom, fn id => (if id = name then SOME (new_phase name) else store id)), trm) |
    InPhase (_, _, _) => raise TERM ("optimization phase already established", [])
  ) thy

fun exit_phase thy = RewriteStore.map (fn state =>
  case state of
    NoPhase _ => raise TERM ("phase already exited", []) |
    InPhase (_, existing, _) => NoPhase existing
  ) thy

end;
\<close>

ML_val \<open>@{term "(case n of
    (BinaryExpr BinAdd (ConstantExpr c_val) e) \<Rightarrow>
      if (\<not>(is_ConstantExpr e) \<and> type e = Integer) then
        success (BinaryExpr BinAdd e (ConstantExpr c_val))
      else
        fail |
    _ \<Rightarrow> fail)"}\<close>


(*(app "_case_syntax"
            (Ast.Variable "x",
             foldr1 (app \<^syntax_const>\<open>_case2\<close>) (map_index (case1 constraint authentic) spec)),
           capp (capps (case_constant, map_index arg1 spec), Ast.Variable "x"))*)

ML \<open>
val test = Conditional
            (@{term \<open>BinaryExpr BinAdd (ConstantExpr c_val) e\<close>},
            @{term \<open>BinaryExpr BinAdd e (ConstantExpr c_val)\<close>},
            @{term \<open>\<not>(is_ConstantExpr e) \<and> type e = Integer\<close>})

fun generate_cases p e ctxt =
  let
  val x =
    Free (singleton (Name.variant_list (fold Term.add_free_names [p, e] [])) "x", dummyT);
  
  val NilC = Syntax.const @{const_name "Nil"};
  val ConsC = Syntax.const @{const_name "Cons"};
  val dummyC = Syntax.const @{const_name "Pure.dummy_pattern"};
  
  fun single x = ConsC $ x $ NilC;
  
  val case1 = Syntax.const \<^syntax_const>\<open>_case1\<close> $ p $ single e;
  val case2 =
    Syntax.const \<^syntax_const>\<open>_case1\<close> $ dummyC $ NilC;
  val cs = Syntax.const \<^syntax_const>\<open>_case2\<close> $ case1 $ case2;
  
  val res = Case_Translation.case_tr false ctxt [x, cs];
  val _ = @{print} res;

  val plz = Syntax.const @{syntax_const "_case_syntax"}
  in             
    single e $ dummyC
  end;

fun rewrite_to_code bind rewrite ctxt =
  case rewrite of
    Conditional (pre, post, cond) => 
        @{const Trueprop} $
        (Const ("HOL.eq", @{typ "(IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> (IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> bool"})
        $ (Free (bind ^ "_code", @{typ "IRExpr \<Rightarrow> RewriteResult"}))
        $ (Const ("IRTreeEval.IRExpr.case_IRExpr",
          @{typ \<open>(IRUnaryOp \<Rightarrow> IRExpr \<Rightarrow> RewriteResult)
           \<Rightarrow> (IRBinaryOp \<Rightarrow> IRExpr \<Rightarrow> IRExpr \<Rightarrow> RewriteResult)
              \<Rightarrow> (IRExpr \<Rightarrow> IRExpr \<Rightarrow> IRExpr \<Rightarrow> RewriteResult)
                 \<Rightarrow> (nat \<Rightarrow> Stamp \<Rightarrow> RewriteResult)
                    \<Rightarrow> (nat \<Rightarrow> Stamp \<Rightarrow> RewriteResult)
                       \<Rightarrow> (Value \<Rightarrow> RewriteResult)
                          \<Rightarrow> (char list \<Rightarrow> RewriteResult)
                             \<Rightarrow> (char list \<Rightarrow> Stamp \<Rightarrow> RewriteResult)
                                \<Rightarrow> IRExpr \<Rightarrow> RewriteResult\<close>})
        $ @{term "(\<lambda> (_::IRUnaryOp) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::IRBinaryOp) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::nat) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::ID) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::Value) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::string) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::string) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}))
 |
   (* Transform (pre, post) => 
        @{const Trueprop}
        $ (Const ("HOL.eq", @{typ "(IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> (IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> bool"})
           $ Free (bind ^ "_code", @{typ "IRExpr \<Rightarrow> RewriteResult"})
           $ generate_cases pre post ctxt
          )
 | *)
    _ => @{const Trueprop} $ 
        (Const ("HOL.eq", @{typ "(IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> (IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> bool"})
        $ (Free (bind ^ "_code", @{typ "IRExpr \<Rightarrow> RewriteResult"}))
        $ @{term \<open>\<lambda> (x::IRExpr) \<Rightarrow> fail\<close>});

fun term_to_rewrite term =
  case term of
    (((Const ("Markup.Rewrite.Transform", _)) $ lhs) $ rhs) => Transform (lhs, rhs)
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ lhs) $ rhs) $ cond) => Conditional (lhs, rhs, cond)
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun rewrite_to_term rewrite = 
  case rewrite of
    Transform (lhs, rhs) => 
      (Const ("Markup.Rewrite.Transform", @{typ "'a => 'a"})) $ lhs $ rhs
    | Conditional (lhs, rhs, cond) => 
      (Const ("Markup.Rewrite.Conditional", @{typ "'a => 'a"})) $ lhs $ rhs $ cond
    | _ => raise TERM ("rewrite cannot be translated yet", [])

fun term_to_obligation ctxt term =
  Syntax.check_prop ctxt (@{const Trueprop} $ (@{const rewrite_obligation} $ term))

fun rewrite_to_termination trm rewrite = 
  case rewrite of
    Transform (lhs, rhs) => (
      @{const Trueprop} 
      $ (Const ("Orderings.ord_class.less", @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"})
      $ (trm $ rhs) $ (trm $ lhs)))
    | Conditional (lhs, rhs, condition) => (
      Const ("Pure.imp", @{typ "prop \<Rightarrow> prop \<Rightarrow> prop"})
      $ (@{const Trueprop} $ condition)
      $ (@{const Trueprop} $ (Const ("Orderings.ord_class.less", @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"})
      $ (trm $ rhs) $ (trm $ lhs))))
    | _ => raise TERM ("rewrite termination generation not implemented", [])

fun register_optimization
  ((bind: binding, _), opt: string) ctxt = 
  let
    val term = Syntax.read_term ctxt opt;

    val rewrite = term_to_rewrite term;

    val obligation = term_to_obligation ctxt term;

    val state = RWList.get (Proof_Context.theory_of ctxt);
    val trm = (case state of
      NoPhase _ => raise TERM ("Optimization phase missing", []) |
      InPhase (_, _, trm) => trm
    );
    val terminating = rewrite_to_termination trm rewrite;

    val name = Binding.name_of bind;

    val register = RWList.add {name=name, rewrite=rewrite};

    val code = rewrite_to_code name rewrite ctxt;

    fun after_qed thms thy =
      let
        val lthy' = Local_Theory.background_theory register thy;

        val (_, lthy'') = Specification.definition
            NONE [] []
            ((Binding.suffix_name "_code" bind, []), code)
            lthy'
      in
        snd (Local_Theory.note ((bind, ([]:Token.src list)), hd thms) lthy'')
      end
  in
    Proof.theorem NONE after_qed [[(obligation, [obligation]), (terminating, [terminating])]] ctxt
  end


val parse_optimization_declaration =
  Parse_Spec.thm_name ":"

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "define an optimization and open proof obligation"
    (parse_optimization_declaration
     -- Parse.term
     >> register_optimization);

fun exit_phase thy =
  Local_Theory.background_theory (RWList.exit_phase) thy

fun begin_phase name trm thy =
  let
    val trm = Syntax.read_term_global thy trm;
  in
    Proof_Context.init_global (RWList.enter_phase name trm thy)
  end

fun
  pretty_rewrite rewrite = Syntax.pretty_term @{context} (rewrite_to_term rewrite)

fun print_optimizations rewrites = 
  let
    fun print_rule tact =
      Pretty.block [
        Pretty.str ( ": "),
        pretty_rewrite (#rewrite tact)
      ];
  in
    [Pretty.big_list "optimizations:" (map print_rule rewrites)]
  end

fun print_phase (phase: phase option) =
  case phase of
    NONE => [Pretty.str "no phase"] |
    SOME phase =>
  [Pretty.str ("phase: " ^ (#name phase))]
  @ (print_optimizations (#rewrites phase))

fun print_phase_state thy =
  case RWList.get (Proof_Context.theory_of thy) of
    NoPhase _ => [Pretty.str "not in a phase"] |
    InPhase (name, (dom, map), _) => print_phase (map name)

fun print_all_phases thy =
  case RWList.get thy of
    NoPhase (dom, store) => 
      List.foldr (fn (name, acc) => print_phase (store name) @ acc) [] dom |
    InPhase (name, (dom, store), _) => List.foldr (fn (name, acc) => print_phase (store name) @ acc) [] dom

fun phase_theory_init name trm thy = 
  Local_Theory.init 
    {background_naming = Sign.naming_of thy,
        setup = begin_phase name trm,
        conclude = exit_phase}
    {define = Generic_Target.define Generic_Target.theory_target_foundation,
        notes = Generic_Target.notes Generic_Target.theory_target_notes,
        abbrev = Generic_Target.abbrev Generic_Target.theory_target_abbrev,
        declaration = K Generic_Target.theory_declaration,
        theory_registration =  Generic_Target.theory_registration,
        locale_dependency = fn _ => error "Not possible in instantiation target",
        pretty = print_phase_state}
    thy

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "instantiate and prove type arity"
   (Parse.name --| Parse.$$$ "trm" -- Parse.const --| Parse.begin
     >> (fn (name, trm) => Toplevel.begin_main_target true (phase_theory_init name trm)));


fun apply_print_optimizations thy =
  (print_all_phases thy |> Pretty.writeln_chunks)


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_optimizations\<close>
    "print debug information for optimizations"
    (Scan.succeed
      (Toplevel.keep (apply_print_optimizations o Toplevel.theory_of)));
\<close>

setup \<open>RWList.reset\<close>

fun bad_trm :: "IRExpr \<Rightarrow> nat" where
  "bad_trm x = 0"

definition test where
  "test n = (case n of
    (BinaryExpr BinAdd (ConstantExpr c_val) e) \<Rightarrow>
      if (\<not>(is_ConstantExpr e) \<and> type e = Integer) then
        success (BinaryExpr BinAdd e (ConstantExpr c_val))
      else
        fail |
    _ \<Rightarrow> fail)"

ML_val \<open>@{term "(case n of
    (BinaryExpr BinAdd (ConstantExpr c_val) e) \<Rightarrow>
      if (\<not>(is_ConstantExpr e) \<and> type e = Integer) then
        success (BinaryExpr BinAdd e (ConstantExpr c_val))
      else
        fail |
    _ \<Rightarrow> fail)"}\<close>

ML_val \<open>@{term "case_IRExpr"}
        $ @{term "(\<lambda> (_::IRUnaryOp) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::IRBinaryOp) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::nat) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::ID) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::Value) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::string) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::string) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}\<close>

ML_val \<open>@{term "hello = case_IRExpr
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)"}\<close>

phase NeverTerminates
  trm bad_trm
begin
  optimization anon:
  "(c1 + c2) \<mapsto> ConstantExpr (intval_add val_c1 val_c2) when True"
    unfolding bad_trm.simps sorry

  print_syntax

  optimization anon2:
  "(c1 + c2) \<mapsto> ConstantExpr (intval_add val_c1 val_c2)"
    unfolding bad_trm.simps sorry

  value "anon_code (BinaryExpr BinAdd (ConstantExpr (IntVal32 0)) (ConstantExpr (IntVal32 0)))"
end


(*
notation BinaryExpr ("_ \<oplus>\<^sub>_ _")

value "x \<oplus>\<^sub>s y"
*)
phase Canonicalization
  trm size
begin

(*
optimization constant_fold:
  "(const(c\<^sub>1) \<oplus>\<^sub>x const(c\<^sub>2)) \<mapsto> (bin_eval c\<^sub>1 x c\<^sub>2)"

optimization constant_add:
  "(e1 + e2) \<mapsto> r when (e1 = ConstantExpr v1 \<and> e2 = ConstantExpr v2 \<and> r = ConstantExpr (intval_add v1 v2))"
  unfolding le_expr_def apply (cases; auto) using evaltree.ConstantExpr defer
   apply simp
  sorry
*)

optimization constant_add:
  "(c1 + c2) \<mapsto> ConstantExpr (intval_add val_c1 val_c2)"
  unfolding le_expr_def apply (cases; auto) using evaltree.ConstantExpr defer
   apply simp
  sorry

value "constant_add_code (BinaryExpr BinAdd (ConstantExpr (IntVal32 0)) (ConstantExpr (IntVal32 0)))"

print_context
print_optimizations

optimization constant_shift:
  "(c + e) \<mapsto> (e + c) when (\<not>(is_ConstantExpr e) \<and> type e = Integer)"
   unfolding rewrite_obligation.simps apply (rule impI) defer apply simp
  sorry

thm constant_shift

optimization neutral_zero:
  "(e + const(0)) \<mapsto> e when (type e = Integer)"
   defer apply simp+
  sorry

ML_val \<open>@{term "(e1 - e2) + e2 \<mapsto> e1"}\<close>

optimization neutral_left_add_sub:
  "(e1 - e2) + e2 \<mapsto> e1"
  sorry

optimization neutral_right_add_sub:
  "e1 + (e2 - e1) \<mapsto> e2"
  sorry

optimization add_ynegate:
  "(x + (-y)) \<mapsto> (x - y) when (type x = Integer \<and> type_safe x y)"
  sorry

print_context
print_optimizations



end

print_context
print_optimizations

phase DirectTranslationTest
  trm size
begin

optimization AbsIdempotence: "abs(abs(e)) \<mapsto> abs(e) when is_IntegerStamp (stamp_expr e)"
  apply auto
  by (metis UnaryExpr abs_abs_is_abs stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(1))

optimization AbsNegate: "abs(-e) \<mapsto> abs(e) when is_IntegerStamp (stamp_expr e)"
  apply auto
  by (metis UnaryExpr abs_neg_is_neg stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(1))

lemma int_constants_valid:
  assumes "is_int_val val"  
  shows "valid_value (constantAsStamp val) val"
  using assms apply (cases val)
  by simp+

lemma unary_eval_preserves_validity:
  assumes "is_int_val c"
  shows "valid_value (constantAsStamp (unary_eval op c)) (unary_eval op c)"
  using assms apply (cases c) apply simp
     defer defer apply simp+
  apply (cases op)
  using int_constants_valid intval_abs.simps(1) is_int_val.simps(1) unary_eval.simps(1) apply presburger
  using int_constants_valid intval_negate.simps(1) is_int_val.simps(1) unary_eval.simps(2) apply presburger
  using int_constants_valid intval_not.simps(1) is_int_val.simps(1) unary_eval.simps(3) apply presburger
  using int_constants_valid is_int_val.simps(1) unary_eval.simps(4) apply presburger
     defer defer defer
     apply (cases op)
  using int_constants_valid intval_abs.simps(2) is_int_val.simps(2) unary_eval.simps(1) apply presburger
  using int_constants_valid intval_negate.simps(2) is_int_val.simps(2) unary_eval.simps(2) apply presburger
  using int_constants_valid intval_not.simps(2) is_int_val.simps(2) unary_eval.simps(3) apply presburger
  sorry (* WARNING: TODO: WARNING: a whole bunch of unary operations aren't implemented making this false *)

optimization UnaryConstantFold: "UnaryExpr op c \<mapsto> ConstantExpr (unary_eval op val_c) when is_int_val val_c"
  apply (auto simp: int_constants_valid)
  using evaltree.ConstantExpr int_constants_valid unary_eval_preserves_validity by simp

optimization AndEqual: "(x & x) \<mapsto> x when is_IntegerStamp (stamp_expr x)"
  apply simp
   apply (metis BinaryExprE CanonicalizeAndProof and_same)
  unfolding size.simps
  by (simp add: size_gt_0)

optimization AndShiftConstantRight: "((ConstantExpr x) + y) \<mapsto> y + (ConstantExpr x) when ~(is_ConstantExpr y)"
  apply simp
   apply (smt (verit, ccfv_threshold) BinaryExprE bin_eval.simps(1) evaltree.simps intval_add_sym)
  unfolding size.simps using nonconstants_gt_one by auto

(*
optimization AndRightFallthrough: "x & y \<mapsto> y when (canBeZero x.stamp & canBeOne y.stamp) = 0" sorry
optimization AndLeftFallthrough: "x & y \<mapsto> x when (canBeZero y.stamp & canBeOne x.stamp) = 0" sorry
*)

lemma neutral_and:
  assumes "valid_value (IntegerStamp 32 lox hix) x"
  shows "bin_eval BinAnd x (IntVal32 (-1)) = x"
  using assms bin_eval.simps(4) by (cases x; auto)

context
  includes bit_operations_syntax
begin
optimization AndNeutral: "(x & (const (NOT 0))) \<mapsto> x when (stamp_expr x = IntegerStamp 32 l u)"
   apply simp
  using neutral_and stamp_implies_valid_value apply auto
  by metis
end

optimization ConditionalEqualBranches: "(b ? v : v) \<mapsto> v"
  apply simp
   apply force
  unfolding size.simps
  by auto

optimization ConditionalEqualIsRHS: "((x == y) ? x : y) \<mapsto> y when (type x = Integer \<and> type_safe x y)"
   apply simp
  apply (smt (verit, del_insts) BinaryExprE CanonicalizeConditionalProof ConditionalExprE cond_eq type_safe_def unfold_type)
  unfolding size.simps by simp
(*
optimization ConditionalEliminateKnownLess: "(x < y ? x : y) \<mapsto> x when (x.stamp.upper <= y.stamp.lower)" sorry
optimization ConditionalEliminateKnownLess: "(x < y ? y : x) \<mapsto> y when (x.stamp.upper <= y.stamp.lower)" sorry
*)

lemma bool_is_int_val:
  "is_int_val (bool_to_val x)"
  using bool_to_val.simps is_int_val.simps by (metis (full_types))

lemma bin_eval_preserves_validity:
  assumes "int_and_equal_bits c1 c2"
  shows "valid_value (constantAsStamp (bin_eval op c1 c2)) (bin_eval op c1 c2)"
  using assms apply (cases c1; cases c2; auto)
     apply (cases op; auto) 
  using int_constants_valid bool_is_int_val
  apply (metis (full_types))
  using int_constants_valid bool_is_int_val
    apply (metis (full_types))
  using int_constants_valid bool_is_int_val
   apply (metis (full_types))
  apply (cases op; auto)  
  using int_constants_valid bool_is_int_val
    apply (metis (full_types))
  using int_constants_valid bool_is_int_val
   apply (metis (full_types))
  using int_constants_valid bool_is_int_val
  by (metis (full_types))


optimization BinaryFoldConstant: "BinaryExpr op (ConstantExpr e1) (ConstantExpr e2) \<mapsto> ConstantExpr (bin_eval op e1 e2) when int_and_equal_bits e1 e2 "
   apply simp using evaltree.BinaryExpr evaltree.ConstantExpr stamp_implies_valid_value
  using bin_eval_preserves_validity 
  apply force using nonconstants_gt_one
  by auto

optimization AddShiftConstantRight: "(c1 + y) \<mapsto> y + c1 when ~(is_ConstantExpr y)"
  apply simp
   apply (smt (verit, del_insts) BinaryExprE bin_eval.simps(1) evaltree.simps intval_add_sym)
  unfolding size.simps using nonconstants_gt_one by simp
(*
optimization RedundantSubAdd: "isAssociative + => (a - b) + b \<mapsto> a" sorry
optimization RedundantAddSub: "isAssociative + => (b + a) - b \<mapsto> a" sorry
*)
lemma neutral_add:
  assumes "valid_value (IntegerStamp 32 lox hix) x"
  shows "bin_eval BinAdd x (IntVal32 (0)) = x"
  using assms bin_eval.simps(4) by (cases x; auto)

optimization AddNeutral: "(e + (const 0)) \<mapsto> e when (stamp_expr e = IntegerStamp 32 l u)"
   apply simp using neutral_add stamp_implies_valid_value 
  using evaltree.BinaryExpr evaltree.ConstantExpr
   apply (metis (no_types, opaque_lifting) BinaryExprE ConstantExprE)
  unfolding size.simps by simp

lemma intval_negateadd_equals_sub_left: "bin_eval BinAdd (unary_eval UnaryNeg e) y = bin_eval BinSub y e"
  by (cases e; auto; cases y; auto)

lemma intval_negateadd_equals_sub_right: "bin_eval BinAdd x (unary_eval UnaryNeg e) = bin_eval BinSub x e"
  by (cases e; auto; cases x; auto)

optimization AddLeftNegateToSub: "-e + y \<mapsto> y - e"
  apply simp using intval_negateadd_equals_sub_left
   apply (metis BinaryExpr BinaryExprE UnaryExprE)
  unfolding size.simps
  by simp

optimization AddRightNegateToSub: "x + -e \<mapsto> x - e"
  apply simp using intval_negateadd_equals_sub_right
   apply (metis BinaryExpr BinaryExprE UnaryExprE)
  unfolding size.simps
  by simp

optimization MulEliminator: "(x * const(0)) \<mapsto> const(0) when (stamp_expr x = IntegerStamp 32 l u)"
   apply simp
  apply (metis BinaryExprE ConstantExprE annihilator_rewrite_helper(1) bin_eval.simps(2) stamp_implies_valid_value)
  unfolding size.simps
  by (simp add: size_gt_0)

optimization MulNeutral: "(x * const(1)) \<mapsto> x when (stamp_expr x = IntegerStamp 32 l u)"
   apply simp
  apply (metis BinaryExprE ConstantExprE bin_eval.simps(2) neutral_rewrite_helper(1) stamp_implies_valid_value)
  unfolding size.simps by simp

(*
optimization MulNegate: "(x * const (-1) ) \<mapsto> -x when (stamp_expr x = IntegerStamp 32 l u)"
  apply simp
  apply (metis BinaryExprE ConstantExprE bin_eval.simps(2) neutral_rewrite_helper(1) stamp_implies_valid_value)
  unfolding size.simps by simp
*)

value "(3::32 word) mod 32"

lemma "(x::nat) \<ge> 0 \<and> x < base \<Longrightarrow> x mod base = x"
  by simp

lemma word_mod_less: "(x::('a::len) word) < base \<Longrightarrow> x mod base = x"
  by (metis mod_less not_le unat_arith_simps(2) unat_arith_simps(7) unat_mono word_le_less_eq)

value "4294967298::32 word"

lemma shift_equality: "((v1::32 word) << unat ((v2::32 word) mod 32)) = v1 * ((2 ^ (unat v2))::32 word)"
proof -
  have "size_class.size (2 ^ (unat v2)) = 32" sorry
  then have "(2 ^ (unat v2)) < 2 ^ 32"
    using uint_range_size sorry
  then have "unat v2 < 32"
    using nat_power_less_imp_less zero_less_numeral by blast
  then show ?thesis
    using \<open>2 ^ unat v2 < 2 ^ 32\<close> numeral_Bit0 power2_eq_square power_add sorry
qed
(*
proof (cases "v2 < 32")
  case True
  have "v2 mod 32 = v2"
    using True
    by (simp add: word_mod_less)
  then show ?thesis
    by simp
next
  case False
  obtain powered where powered_def: "(powered::32 word) = 2 ^ (unat v2)"
    by auto
  have "powered < (2 ^ 32)"
    sorry
  then have "powered mod (2 ^ 32) = powered"
    using word_mod_less
    by blast
  then have "v2 mod 32 = v2"
    unfolding powered_def sorry
  then show ?thesis unfolding powered_def sorry
qed

lemma intval_shift_equality:
  shows "intval_mul (IntVal32 x) (IntVal32 (2^(unat j))) = intval_left_shift (IntVal32 x) (IntVal32 j)"
  unfolding intval_mul.simps intval_left_shift.simps
  by (simp add: shift_equality)

lemma bin_shift_equality:
  "bin_eval BinMul (IntVal32 x) (IntVal32 (2^(unat j))) = bin_eval BinLeftShift (IntVal32 x) (IntVal32 j)"
  using intval_shift_equality by simp

optimization MulPower2: "(x * const(2^(unat j))) \<mapsto> x << const(j) when (stamp_expr x = IntegerStamp 32 l u)"
   apply simp
  using BinaryExprE ConstantExprE bin_eval.simps(2,7) stamp_implies_valid_value intval_shift_equality
  sorry
*)

print_context
print_optimizations
end

print_optimizations

end
