section \<open>Testing of IR Semantics based on GraalVM Unit Tests\<close>

theory UnitTesting
  imports
    IRStepObj
begin

declare [[ML_source_trace]]

inductive static_test :: "IRGraph \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>state = new_map ps;
    (\<lambda>x. Some g) \<turnstile> ([('''', 0, state), ('''', 0, state)], new_heap) | [] \<longrightarrow>* ((end # xs), heap) | l \<rbrakk>
    \<Longrightarrow> static_test g ps (m_val (prod.snd (prod.snd end)) 0)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testE) static_test .


(* gr1 *)
definition gr1 :: IRGraph where
  "gr1 = irgraph [
  (0, (StartNode  (Some 2) 5), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 42)), default_stamp),
  (4, (AddNode 1 3), default_stamp),
  (5, (ReturnNode  (Some 3)  None), default_stamp)
  ]"
value "static_test gr1 [(IntVal 32 17)] (IntVal 32 42)"
 

end