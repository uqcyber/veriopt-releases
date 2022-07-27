theory ArithmeticTesting
imports Semantics.IRStepObj
begin

declare [[ML_source_trace]]

inductive static_test :: "IRGraph \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>config0 = (g, 0, new_map_state, ps);
    (\<lambda>x. None) \<turnstile> ([config0, config0], new_heap) | [] \<longrightarrow>* ((end # xs), heap) | l \<rbrakk>
    \<Longrightarrow> static_test g ps ((prod.fst(prod.snd(prod.snd end))) 0)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testE) static_test .

definition arith_test_AddNode32 :: IRGraph where
  "arith_test_AddNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (2147483644))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (4))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (3))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (3))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (2147483644))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_AddNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (-4))" by eval

definition arith_test_AddNode64 :: IRGraph where
  "arith_test_AddNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (AddNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775804))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (4))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (3))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (3))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (9223372036854775804))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AddNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval

definition arith_test_MulNode32 :: IRGraph where
  "arith_test_MulNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (MulNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (4))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (4))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (4))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (4))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_MulNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (4))" by eval

definition arith_test_MulNode64 :: IRGraph where
  "arith_test_MulNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (MulNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (4))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_MulNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval

definition arith_test_SubNode32 :: IRGraph where
  "arith_test_SubNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (SubNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (3))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (-2147483644))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (2147483644))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (3))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (4))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (3))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SubNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (0))" by eval

definition arith_test_SubNode64 :: IRGraph where
  "arith_test_SubNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (SubNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775804))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (3))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (9223372036854775804))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (4))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (3))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (3))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SubNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval

definition arith_test_AndNode32 :: IRGraph where
  "arith_test_AndNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (AndNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_AndNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (-2))" by eval

definition arith_test_AndNode64 :: IRGraph where
  "arith_test_AndNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (AndNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_AndNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval

definition arith_test_OrNode32 :: IRGraph where
  "arith_test_OrNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (OrNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (3))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (3))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_OrNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (-2))" by eval

definition arith_test_OrNode64 :: IRGraph where
  "arith_test_OrNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (OrNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (3))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (3))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_OrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval

definition arith_test_XorNode32 :: IRGraph where
  "arith_test_XorNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (XorNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (2147483644))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (2147483644))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (2147483645))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (-2147483645))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (3))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (3))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_XorNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (0))" by eval

definition arith_test_XorNode64 :: IRGraph where
  "arith_test_XorNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (XorNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775804))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (9223372036854775804))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (9223372036854775805))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (3))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (3))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775805))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (1))" by eval
lemma "static_test arith_test_XorNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval

definition arith_test_ShortCircuitOrNode32 :: IRGraph where
  "arith_test_ShortCircuitOrNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (ShortCircuitOrNode 1 2), IntegerStamp 32 0 1),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 0 1)
   ]"
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (1))" by eval

definition arith_test_ShortCircuitOrNode64 :: IRGraph where
  "arith_test_ShortCircuitOrNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (ShortCircuitOrNode 1 2), IntegerStamp 32 0 1),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 0 1)
   ]"
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_ShortCircuitOrNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval

definition arith_test_LeftShiftNode32 :: IRGraph where
  "arith_test_LeftShiftNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (LeftShiftNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (-8))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (8))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (-8))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_LeftShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (-2147483648))" by eval

definition arith_test_LeftShiftNode64 :: IRGraph where
  "arith_test_LeftShiftNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (LeftShiftNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (-8))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (8))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (-8))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (1))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-4))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (1))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_LeftShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval

definition arith_test_RightShiftNode32 :: IRGraph where
  "arith_test_RightShiftNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (RightShiftNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (2))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (536870911))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (536870911))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (-536870912))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (-536870912))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (2))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_RightShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (-1))" by eval

definition arith_test_RightShiftNode64 :: IRGraph where
  "arith_test_RightShiftNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (RightShiftNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (2305843009213693951))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (2305843009213693951))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (-2305843009213693952))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (-2305843009213693952))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (2))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (2))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_RightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval

definition arith_test_UnsignedRightShiftNode32 :: IRGraph where
  "arith_test_UnsignedRightShiftNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (UnsignedRightShiftNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (3))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (3))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (536870911))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (536870911))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (536870912))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (536870912))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (3))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (3))" by eval

definition arith_test_UnsignedRightShiftNode64 :: IRGraph where
  "arith_test_UnsignedRightShiftNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (UnsignedRightShiftNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (3))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (3))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (2305843009213693951))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (2305843009213693951))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (2305843009213693952))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (2305843009213693952))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal64 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (3))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (3))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_UnsignedRightShiftNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval

definition arith_test_IntegerEqualsNode32 :: IRGraph where
  "arith_test_IntegerEqualsNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (IntegerEqualsNode 1 2), IntegerStamp 32 0 1),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 0 1)
   ]"
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (1))" by eval

definition arith_test_IntegerEqualsNode64 :: IRGraph where
  "arith_test_IntegerEqualsNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (IntegerEqualsNode 1 2), IntegerStamp 32 0 1),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 0 1)
   ]"
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerEqualsNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval

definition arith_test_IntegerLessThanNode32 :: IRGraph where
  "arith_test_IntegerLessThanNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (IntegerLessThanNode 1 2), IntegerStamp 32 0 1),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 0 1)
   ]"
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (0))" by eval

definition arith_test_IntegerLessThanNode64 :: IRGraph where
  "arith_test_IntegerLessThanNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (IntegerLessThanNode 1 2), IntegerStamp 32 0 1),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 0 1)
   ]"
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerLessThanNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval

definition arith_test_IntegerBelowNode32 :: IRGraph where
  "arith_test_IntegerBelowNode32 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (IntegerBelowNode 1 2), IntegerStamp 32 0 1),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 0 1)
   ]"
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (0))" by eval

definition arith_test_IntegerBelowNode64 :: IRGraph where
  "arith_test_IntegerBelowNode64 = irgraph [
    (0, (StartNode (Some 3) 5), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (IntegerBelowNode 1 2), IntegerStamp 32 0 1),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 0 1)
   ]"
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal32 (1))" by eval
lemma "static_test arith_test_IntegerBelowNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal32 (0))" by eval


definition arith_test_SignedDivNode32 :: IRGraph where
  "arith_test_SignedDivNode32 = irgraph [
    (0, (StartNode (Some 3) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (-1073741823))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (-1073741824))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (-1073741823))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (-1073741823))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (1073741823))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (1073741824))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedDivNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (1))" by eval

definition arith_test_SignedDivNode64 :: IRGraph where
  "arith_test_SignedDivNode64 = irgraph [
    (0, (StartNode (Some 3) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (-4611686018427387903))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (-4611686018427387904))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (-4611686018427387903))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-4611686018427387903))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (4611686018427387903))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (4611686018427387904))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedDivNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (1))" by eval

definition arith_test_SignedRemNode32 :: IRGraph where
  "arith_test_SignedRemNode32 = irgraph [
    (0, (StartNode (Some 3) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (SignedRemNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483646))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2)), (IntVal32 (2147483646))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (1)), (IntVal32 (2147483646))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (0)), (IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-1)), (IntVal32 (2147483646))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2)), (IntVal32 (2147483646))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483646)), (IntVal32 (2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483647)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483648)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2)), (IntVal32 (2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (1)), (IntVal32 (2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (0)), (IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-1)), (IntVal32 (2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2)), (IntVal32 (2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2)), (IntVal32 (-2147483647))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (1)), (IntVal32 (-2147483647))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (0)), (IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-1)), (IntVal32 (-2147483647))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2)), (IntVal32 (-2147483647))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483646)), (IntVal32 (-2147483648))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483647)), (IntVal32 (-2147483648))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2147483648))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2)), (IntVal32 (-2147483648))] (IntVal32 (2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (1)), (IntVal32 (-2147483648))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (0)), (IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-1)), (IntVal32 (-2147483648))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2)), (IntVal32 (-2147483648))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483646)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483647)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483647)), (IntVal32 (2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483648)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (1)), (IntVal32 (2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (0)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-1)), (IntVal32 (2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2)), (IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483646)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483647)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483647)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483648)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (0)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-1)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2)), (IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483646)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483647)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483647)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483648)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (0)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-1)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2)), (IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483646)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2147483647)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483647)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2147483648)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (2)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (1)), (IntVal32 (-2))] (IntVal32 (1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (0)), (IntVal32 (-2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-1)), (IntVal32 (-2))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_SignedRemNode32 [(IntVal32 (-2)), (IntVal32 (-2))] (IntVal32 (0))" by eval

definition arith_test_SignedRemNode64 :: IRGraph where
  "arith_test_SignedRemNode64 = irgraph [
    (0, (StartNode (Some 3) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (3, (FrameState [] None None None), IllegalStamp),
    (4, (SignedRemNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (5, (ReturnNode (Some 4) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775806))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775806))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775806))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775806))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775806))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (2)), (IntVal64 (9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (1)), (IntVal64 (9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (0)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-2)), (IntVal64 (9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-1)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (2)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (1)), (IntVal64 (2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (0)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-2)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-1)), (IntVal64 (2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (2)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (1)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (0)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-2)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-1)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (2)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (1)), (IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (0)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-2)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-1)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-2))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (2)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (1)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (0)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-2)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-1)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775807))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775807))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775807))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775807))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775806)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (2)), (IntVal64 (-9223372036854775808))] (IntVal64 (2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (1)), (IntVal64 (-9223372036854775808))] (IntVal64 (1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (0)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-2)), (IntVal64 (-9223372036854775808))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-1)), (IntVal64 (-9223372036854775808))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775807)), (IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_SignedRemNode64 [(IntVal64 (-9223372036854775808)), (IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval

definition arith_test_AbsNode32 :: IRGraph where
  "arith_test_AbsNode32 = irgraph [
    (0, (StartNode (Some 2) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (FrameState [] None None None), IllegalStamp),
    (3, (AbsNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (4, (ReturnNode (Some 3) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_AbsNode32 [(IntVal32 (2147483646))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_AbsNode32 [(IntVal32 (2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AbsNode32 [(IntVal32 (-2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_AbsNode32 [(IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_AbsNode32 [(IntVal32 (2))] (IntVal32 (2))" by eval
lemma "static_test arith_test_AbsNode32 [(IntVal32 (1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AbsNode32 [(IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_AbsNode32 [(IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_AbsNode32 [(IntVal32 (-2))] (IntVal32 (2))" by eval

definition arith_test_AbsNode64 :: IRGraph where
  "arith_test_AbsNode64 = irgraph [
    (0, (StartNode (Some 2) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (FrameState [] None None None), IllegalStamp),
    (3, (AbsNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (4, (ReturnNode (Some 3) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_AbsNode64 [(IntVal64 (9223372036854775806))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_AbsNode64 [(IntVal64 (9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AbsNode64 [(IntVal64 (2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AbsNode64 [(IntVal64 (1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AbsNode64 [(IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_AbsNode64 [(IntVal64 (-2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_AbsNode64 [(IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_AbsNode64 [(IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_AbsNode64 [(IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval

definition arith_test_NegateNode32 :: IRGraph where
  "arith_test_NegateNode32 = irgraph [
    (0, (StartNode (Some 2) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (FrameState [] None None None), IllegalStamp),
    (3, (NegateNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (4, (ReturnNode (Some 3) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_NegateNode32 [(IntVal32 (2147483646))] (IntVal32 (-2147483646))" by eval
lemma "static_test arith_test_NegateNode32 [(IntVal32 (2147483647))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_NegateNode32 [(IntVal32 (-2147483647))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_NegateNode32 [(IntVal32 (-2147483648))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_NegateNode32 [(IntVal32 (2))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_NegateNode32 [(IntVal32 (1))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_NegateNode32 [(IntVal32 (0))] (IntVal32 (0))" by eval
lemma "static_test arith_test_NegateNode32 [(IntVal32 (-1))] (IntVal32 (1))" by eval
lemma "static_test arith_test_NegateNode32 [(IntVal32 (-2))] (IntVal32 (2))" by eval

definition arith_test_NegateNode64 :: IRGraph where
  "arith_test_NegateNode64 = irgraph [
    (0, (StartNode (Some 2) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (FrameState [] None None None), IllegalStamp),
    (3, (NegateNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (4, (ReturnNode (Some 3) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_NegateNode64 [(IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775806))" by eval
lemma "static_test arith_test_NegateNode64 [(IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_NegateNode64 [(IntVal64 (2))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_NegateNode64 [(IntVal64 (1))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_NegateNode64 [(IntVal64 (0))] (IntVal64 (0))" by eval
lemma "static_test arith_test_NegateNode64 [(IntVal64 (-2))] (IntVal64 (2))" by eval
lemma "static_test arith_test_NegateNode64 [(IntVal64 (-1))] (IntVal64 (1))" by eval
lemma "static_test arith_test_NegateNode64 [(IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775807))" by eval
lemma "static_test arith_test_NegateNode64 [(IntVal64 (-9223372036854775808))] (IntVal64 (-9223372036854775808))" by eval

definition arith_test_NotNode32 :: IRGraph where
  "arith_test_NotNode32 = irgraph [
    (0, (StartNode (Some 2) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (FrameState [] None None None), IllegalStamp),
    (3, (NotNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (4, (ReturnNode (Some 3) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_NotNode32 [(IntVal32 (2147483646))] (IntVal32 (-2147483647))" by eval
lemma "static_test arith_test_NotNode32 [(IntVal32 (2147483647))] (IntVal32 (-2147483648))" by eval
lemma "static_test arith_test_NotNode32 [(IntVal32 (-2147483647))] (IntVal32 (2147483646))" by eval
lemma "static_test arith_test_NotNode32 [(IntVal32 (-2147483648))] (IntVal32 (2147483647))" by eval
lemma "static_test arith_test_NotNode32 [(IntVal32 (2))] (IntVal32 (-3))" by eval
lemma "static_test arith_test_NotNode32 [(IntVal32 (1))] (IntVal32 (-2))" by eval
lemma "static_test arith_test_NotNode32 [(IntVal32 (0))] (IntVal32 (-1))" by eval
lemma "static_test arith_test_NotNode32 [(IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_NotNode32 [(IntVal32 (-2))] (IntVal32 (1))" by eval

definition arith_test_NotNode64 :: IRGraph where
  "arith_test_NotNode64 = irgraph [
    (0, (StartNode (Some 2) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (FrameState [] None None None), IllegalStamp),
    (3, (NotNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (4, (ReturnNode (Some 3) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_NotNode64 [(IntVal64 (9223372036854775806))] (IntVal64 (-9223372036854775807))" by eval
lemma "static_test arith_test_NotNode64 [(IntVal64 (9223372036854775807))] (IntVal64 (-9223372036854775808))" by eval
lemma "static_test arith_test_NotNode64 [(IntVal64 (2))] (IntVal64 (-3))" by eval
lemma "static_test arith_test_NotNode64 [(IntVal64 (1))] (IntVal64 (-2))" by eval
lemma "static_test arith_test_NotNode64 [(IntVal64 (0))] (IntVal64 (-1))" by eval
lemma "static_test arith_test_NotNode64 [(IntVal64 (-2))] (IntVal64 (1))" by eval
lemma "static_test arith_test_NotNode64 [(IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_NotNode64 [(IntVal64 (-9223372036854775807))] (IntVal64 (9223372036854775806))" by eval
lemma "static_test arith_test_NotNode64 [(IntVal64 (-9223372036854775808))] (IntVal64 (9223372036854775807))" by eval

definition arith_test_LogicNegationNode32 :: IRGraph where
  "arith_test_LogicNegationNode32 = irgraph [
    (0, (StartNode (Some 2) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
    (2, (FrameState [] None None None), IllegalStamp),
    (3, (LogicNegationNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
    (4, (ReturnNode (Some 3) None), IntegerStamp 32 (-2147483648) (2147483647))
   ]"
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (2147483646))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (-2147483647))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (-2147483648))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (2))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (0))] (IntVal32 (1))" by eval
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (-1))] (IntVal32 (0))" by eval
lemma "static_test arith_test_LogicNegationNode32 [(IntVal32 (-2))] (IntVal32 (0))" by eval

definition arith_test_LogicNegationNode64 :: IRGraph where
  "arith_test_LogicNegationNode64 = irgraph [
    (0, (StartNode (Some 2) 4), VoidStamp),
    (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (2, (FrameState [] None None None), IllegalStamp),
    (3, (LogicNegationNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
    (4, (ReturnNode (Some 3) None), IntegerStamp 64 (-9223372036854775808) (9223372036854775807))
   ]"
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (9223372036854775806))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (0))] (IntVal64 (1))" by eval
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (-2))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (-1))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (-9223372036854775807))] (IntVal64 (0))" by eval
lemma "static_test arith_test_LogicNegationNode64 [(IntVal64 (-9223372036854775808))] (IntVal64 (0))" by eval

end
