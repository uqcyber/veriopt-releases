theory AssertTesting
imports Semantics.IRStepObj
begin

declare [[ML_source_trace]]

(* Heap with asserts enabled *)
definition assertEnabledHeap :: FieldRefHeap where
  "assertEnabledHeap = h_store_field ''VerifyProgram.$assertionsDisabled'' None (IntVal32 0) new_heap"

(* Dependencies for the AssertionError class *)
definition assertClass :: Program where
"assertClass = Map.empty
(''java.lang.AssertionError.<init>()V'' \<mapsto> irgraph [
 (0, (StartNode (None) (3)), VoidStamp),
 (1, (ParameterNode 0), VoidStamp),
 (2, (ConstantNode (ObjStr ''no details provided'')), VoidStamp),
 (3, (StoreFieldNode 3 ''assertFailure'' 2 None (Some 1) 4), VoidStamp),
 (4, (ReturnNode (None) (None)), VoidStamp)])
(''java.lang.AssertionError.<init>(Ljava/lang/Object;)V'' \<mapsto> irgraph [
 (0, (StartNode (None) (3)), VoidStamp),
 (1, (ParameterNode 0), VoidStamp),
 (2, (ParameterNode 1), VoidStamp),
 (3, (StoreFieldNode 3 ''assertFailure'' 2 None (Some 1) 4), VoidStamp),
 (4, (ReturnNode (None) (None)), VoidStamp)])"


datatype ExitCause =
  NormalReturn |
  Exception ID Value

inductive assert_test :: "Program 
      \<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> Value list) list \<times> FieldRefHeap
      \<Rightarrow> ExitCause
      \<Rightarrow> bool"
  for p where
  "\<lbrakk>kind g nid = (UnwindNode exception);
    g \<turnstile> exception \<triangleright> ex;
    [m, ps] \<turnstile> ex \<mapsto> ObjRef e;
    details = h_load_field ''assertFailure'' e h\<rbrakk>
    \<Longrightarrow> assert_test p (((g,nid,m,ps)#stk),h) (Exception exception details)" |

  "\<lbrakk>p \<turnstile> (((g,nid,m,ps)#stk),h) \<longrightarrow> (((g',nid',m',ps')#stk'),h');
    assert_test p (((g',nid',m',ps')#stk'),h') es\<rbrakk> 
    \<Longrightarrow> assert_test p (((g,nid,m,ps)#stk),h) es" |

  "\<lbrakk>p \<turnstile> (((g,nid,m,ps)#stk),h) \<longrightarrow> (((g',nid',m',ps')#stk'),h');
    has_return m'\<rbrakk>
    \<Longrightarrow> assert_test p (((g,nid,m,ps)#stk),h) NormalReturn"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as assertTest,
                  i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as assertTestOut)
          "assert_test" .



definition prog :: Program where
"prog = assertClass
(''VerifyProgram.verify()V'' \<mapsto> irgraph [
 (0, (StartNode ((Some 1)) (2)), VoidStamp),
 (1, (FrameState ([]) (None) (None) (None)), IllegalStamp),
 (2, (LoadFieldNode (2) (''VerifyProgram.$assertionsDisabled'') (None) (7)), IntegerStamp 32 (0) (1)),
 (3, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
 (4, (IntegerEqualsNode (2) (3)), VoidStamp),
 (5, (BeginNode (20)), VoidStamp),
 (6, (BeginNode (15)), VoidStamp),
 (7, (IfNode (4) (6) (5)), VoidStamp),
 (8, (ConstantNode (IntVal32 (10))), IntegerStamp 32 (10) (10)),
 (9, (ConstantNode (IntVal32 (4))), IntegerStamp 32 (4) (4)),
 (10, (ConstantNode (IntVal32 (6))), IntegerStamp 32 (6) (6)),
 (11, (MethodCallTargetNode (''VerifyProgram.add(II)I'') ([9, 10])), VoidStamp),
 (12, (ExceptionObjectNode ((Some 13)) (30)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (13, (FrameState ([]) (None) ((Some [12])) (None)), IllegalStamp),
 (15, (InvokeWithExceptionNode (15) (11) (None) (None) ((Some 16)) (17) (12)), IntegerStamp 32 (-2147483648) (2147483647)),
 (16, (FrameState ([]) (None) ((Some [8, 15])) (None)), IllegalStamp),
 (17, (KillingBeginNode (24)), VoidStamp),
 (18, (IntegerEqualsNode (15) (8)), VoidStamp),
 (19, (BeginNode (25)), VoidStamp),
 (20, (EndNode), VoidStamp),
 (21, (MergeNode ([20, 22]) ((Some 39)) (40)), VoidStamp),
 (22, (EndNode), VoidStamp),
 (23, (BeginNode (22)), VoidStamp),
 (24, (IfNode (18) (23) (19)), VoidStamp),
 (25, (NewInstanceNode (25) (''java.lang.AssertionError'') (None) (34)), ObjectStamp ''Ljava/lang/AssertionError;'' True True False),
 (26, (ConstantNode (ObjStr ''4 + 6 != 10'')), ObjectStamp ''Ljava/lang/String;'' True True False),
 (27, (MethodCallTargetNode (''java.lang.AssertionError.<init>(Ljava/lang/Object;)V'') ([25, 26])), VoidStamp),
 (28, (ExceptionObjectNode ((Some 29)) (32)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (29, (FrameState ([]) (None) ((Some [28])) (None)), IllegalStamp),
 (30, (EndNode), VoidStamp),
 (31, (MergeNode ([30, 32, 38, 51, 66, 71, 83, 98, 103, 115, 130, 135]) ((Some 138)) (139)), VoidStamp),
 (32, (EndNode), VoidStamp),
 (33, (ValuePhiNode (33) ([12, 28, 25, 49, 64, 62, 81, 96, 94, 113, 128, 126, 138]) (31)), ObjectStamp '''' False False False),
 (34, (InvokeWithExceptionNode (34) (27) (None) (None) ((Some 35)) (36) (28)), VoidStamp),
 (35, (FrameState ([]) (None) ((Some [25])) (None)), IllegalStamp),
 (36, (KillingBeginNode (38)), VoidStamp),
 (38, (EndNode), VoidStamp),
 (39, (FrameState ([]) (None) (None) (None)), IllegalStamp),
 (40, (LoadFieldNode (40) (''VerifyProgram.$assertionsDisabled'') (None) (44)), IntegerStamp 32 (0) (1)),
 (41, (IntegerEqualsNode (40) (3)), VoidStamp),
 (42, (BeginNode (57)), VoidStamp),
 (43, (BeginNode (52)), VoidStamp),
 (44, (IfNode (41) (43) (42)), VoidStamp),
 (45, (ConstantNode (IntVal32 (100))), IntegerStamp 32 (100) (100)),
 (46, (ConstantNode (IntVal32 (20))), IntegerStamp 32 (20) (20)),
 (47, (ConstantNode (IntVal32 (80))), IntegerStamp 32 (80) (80)),
 (48, (MethodCallTargetNode (''VerifyProgram.add(II)I'') ([46, 47])), VoidStamp),
 (49, (ExceptionObjectNode ((Some 50)) (51)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (50, (FrameState ([]) (None) ((Some [49])) (None)), IllegalStamp),
 (51, (EndNode), VoidStamp),
 (52, (InvokeWithExceptionNode (52) (48) (None) (None) ((Some 53)) (54) (49)), IntegerStamp 32 (-2147483648) (2147483647)),
 (53, (FrameState ([]) (None) ((Some [45, 52])) (None)), IllegalStamp),
 (54, (KillingBeginNode (61)), VoidStamp),
 (55, (IntegerEqualsNode (52) (45)), VoidStamp),
 (56, (BeginNode (62)), VoidStamp),
 (57, (EndNode), VoidStamp),
 (58, (MergeNode ([57, 59]) ((Some 72)) (73)), VoidStamp),
 (59, (EndNode), VoidStamp),
 (60, (BeginNode (59)), VoidStamp),
 (61, (IfNode (55) (60) (56)), VoidStamp),
 (62, (NewInstanceNode (62) (''java.lang.AssertionError'') (None) (67)), ObjectStamp ''Ljava/lang/AssertionError;'' True True False),
 (63, (MethodCallTargetNode (''java.lang.AssertionError.<init>()V'') ([62])), VoidStamp),
 (64, (ExceptionObjectNode ((Some 65)) (66)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (65, (FrameState ([]) (None) ((Some [64])) (None)), IllegalStamp),
 (66, (EndNode), VoidStamp),
 (67, (InvokeWithExceptionNode (67) (63) (None) (None) ((Some 68)) (69) (64)), VoidStamp),
 (68, (FrameState ([]) (None) ((Some [62])) (None)), IllegalStamp),
 (69, (KillingBeginNode (71)), VoidStamp),
 (71, (EndNode), VoidStamp),
 (72, (FrameState ([]) (None) (None) (None)), IllegalStamp),
 (73, (LoadFieldNode (73) (''VerifyProgram.$assertionsDisabled'') (None) (77)), IntegerStamp 32 (0) (1)),
 (74, (IntegerEqualsNode (73) (3)), VoidStamp),
 (75, (BeginNode (89)), VoidStamp),
 (76, (BeginNode (84)), VoidStamp),
 (77, (IfNode (74) (76) (75)), VoidStamp),
 (78, (ConstantNode (IntVal32 (99))), IntegerStamp 32 (99) (99)),
 (79, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
 (80, (MethodCallTargetNode (''VerifyProgram.add(II)I'') ([78, 79])), VoidStamp),
 (81, (ExceptionObjectNode ((Some 82)) (83)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (82, (FrameState ([]) (None) ((Some [81])) (None)), IllegalStamp),
 (83, (EndNode), VoidStamp),
 (84, (InvokeWithExceptionNode (84) (80) (None) (None) ((Some 85)) (86) (81)), IntegerStamp 32 (-2147483648) (2147483647)),
 (85, (FrameState ([]) (None) ((Some [45, 84])) (None)), IllegalStamp),
 (86, (KillingBeginNode (93)), VoidStamp),
 (87, (IntegerEqualsNode (84) (45)), VoidStamp),
 (88, (BeginNode (94)), VoidStamp),
 (89, (EndNode), VoidStamp),
 (90, (MergeNode ([89, 91]) ((Some 104)) (105)), VoidStamp),
 (91, (EndNode), VoidStamp),
 (92, (BeginNode (91)), VoidStamp),
 (93, (IfNode (87) (92) (88)), VoidStamp),
 (94, (NewInstanceNode (94) (''java.lang.AssertionError'') (None) (99)), ObjectStamp ''Ljava/lang/AssertionError;'' True True False),
 (95, (MethodCallTargetNode (''java.lang.AssertionError.<init>()V'') ([94])), VoidStamp),
 (96, (ExceptionObjectNode ((Some 97)) (98)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (97, (FrameState ([]) (None) ((Some [96])) (None)), IllegalStamp),
 (98, (EndNode), VoidStamp),
 (99, (InvokeWithExceptionNode (99) (95) (None) (None) ((Some 100)) (101) (96)), VoidStamp),
 (100, (FrameState ([]) (None) ((Some [94])) (None)), IllegalStamp),
 (101, (KillingBeginNode (103)), VoidStamp),
 (103, (EndNode), VoidStamp),
 (104, (FrameState ([]) (None) (None) (None)), IllegalStamp),
 (105, (LoadFieldNode (105) (''VerifyProgram.$assertionsDisabled'') (None) (109)), IntegerStamp 32 (0) (1)),
 (106, (IntegerEqualsNode (105) (3)), VoidStamp),
 (107, (BeginNode (121)), VoidStamp),
 (108, (BeginNode (116)), VoidStamp),
 (109, (IfNode (106) (108) (107)), VoidStamp),
 (110, (ConstantNode (IntVal32 (23))), IntegerStamp 32 (23) (23)),
 (111, (ConstantNode (IntVal32 (3))), IntegerStamp 32 (3) (3)),
 (112, (MethodCallTargetNode (''VerifyProgram.add(II)I'') ([46, 111])), VoidStamp),
 (113, (ExceptionObjectNode ((Some 114)) (115)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (114, (FrameState ([]) (None) ((Some [113])) (None)), IllegalStamp),
 (115, (EndNode), VoidStamp),
 (116, (InvokeWithExceptionNode (116) (112) (None) (None) ((Some 117)) (118) (113)), IntegerStamp 32 (-2147483648) (2147483647)),
 (117, (FrameState ([]) (None) ((Some [110, 116])) (None)), IllegalStamp),
 (118, (KillingBeginNode (125)), VoidStamp),
 (119, (IntegerEqualsNode (116) (110)), VoidStamp),
 (120, (BeginNode (126)), VoidStamp),
 (121, (EndNode), VoidStamp),
 (122, (MergeNode ([121, 123]) ((Some 136)) (137)), VoidStamp),
 (123, (EndNode), VoidStamp),
 (124, (BeginNode (123)), VoidStamp),
 (125, (IfNode (119) (124) (120)), VoidStamp),
 (126, (NewInstanceNode (126) (''java.lang.AssertionError'') (None) (131)), ObjectStamp ''Ljava/lang/AssertionError;'' True True False),
 (127, (MethodCallTargetNode (''java.lang.AssertionError.<init>()V'') ([126])), VoidStamp),
 (128, (ExceptionObjectNode ((Some 129)) (130)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (129, (FrameState ([]) (None) ((Some [128])) (None)), IllegalStamp),
 (130, (EndNode), VoidStamp),
 (131, (InvokeWithExceptionNode (131) (127) (None) (None) ((Some 132)) (133) (128)), VoidStamp),
 (132, (FrameState ([]) (None) ((Some [126])) (None)), IllegalStamp),
 (133, (KillingBeginNode (135)), VoidStamp),
 (135, (EndNode), VoidStamp),
 (136, (FrameState ([]) (None) (None) (None)), IllegalStamp),
 (137, (ReturnNode (None) (None)), VoidStamp),
 (138, (FrameState ([]) (None) ((Some [33])) (None)), IllegalStamp),
 (139, (UnwindNode (33)), VoidStamp)])
(''VerifyProgram.add(II)I'' \<mapsto> irgraph [
 (0, (StartNode ((Some 3)) (5)), VoidStamp),
 (1, (ParameterNode (0)), IntegerStamp 32 (-2147483648) (2147483647)),
 (2, (ParameterNode (1)), IntegerStamp 32 (-2147483648) (2147483647)),
 (3, (FrameState ([]) (None) ((Some [1, 2])) (None)), IllegalStamp),
 (4, (AddNode (1) (2)), IntegerStamp 32 (-2147483648) (2147483647)),
 (5, (ReturnNode ((Some 4)) (None)), VoidStamp)])
"

definition prog_state0 where
  "prog_state0 = (the (prog ''VerifyProgram.verify()V''), 0, new_map_state, [])"
value "assert_test prog ([prog_state0,prog_state0], assertEnabledHeap) NormalReturn"

values "{m | m . assert_test prog ([(the (prog ''VerifyProgram.verify()V''), 0, new_map_state, [])], assertEnabledHeap) m}"


end