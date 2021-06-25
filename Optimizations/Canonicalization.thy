section \<open>Canonicalization Phase\<close>

theory Canonicalization
  imports 
    Proofs.IRGraphFrames
    Proofs.Stuttering
    Proofs.Bisimulation
    Proofs.Form

    Graph.Traversal
begin

inductive CanonicalizeConditional :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" where
  negate_condition: (* ConditionalNode.findSynonym (252) *)
  "\<lbrakk>kind g cond = LogicNegationNode flip\<rbrakk>
  \<Longrightarrow> CanonicalizeConditional g (ConditionalNode cond tb fb) (ConditionalNode flip fb tb)" |
  
  const_true: (* ConditionalNode.findSynonym (258) *)
  "\<lbrakk>kind g cond = ConstantNode val;
    val_to_bool val\<rbrakk>
  \<Longrightarrow> CanonicalizeConditional g (ConditionalNode cond tb fb) (RefNode tb)" |

  const_false: (* ConditionalNode.findSynonym (256) *)
  "\<lbrakk>kind g cond = ConstantNode val;
    \<not>(val_to_bool val)\<rbrakk>
  \<Longrightarrow> CanonicalizeConditional g (ConditionalNode cond tb fb) (RefNode fb)" |

  eq_branches: (* ConditionalNode.canonicalizeConditional (151) *)
  "\<lbrakk>tb = fb\<rbrakk>
  \<Longrightarrow> CanonicalizeConditional g (ConditionalNode cond tb fb) (RefNode tb)" |

  cond_eq: (* ConditionalNode.canonicalizeConditional (155) *)
  "\<lbrakk>kind g cond = IntegerEqualsNode tb fb\<rbrakk>
  \<Longrightarrow> CanonicalizeConditional g (ConditionalNode cond tb fb) (RefNode fb)" |

  condition_bounds_x: (* ConditionalNode.canonicalizeConditional (169) *)
  "\<lbrakk>kind g cond = IntegerLessThanNode tb fb;
    stpi_upper (stamp g tb) < stpi_lower (stamp g fb)\<rbrakk>
  \<Longrightarrow> CanonicalizeConditional g (ConditionalNode cond tb fb) (RefNode tb)" |

  condition_bounds_y: (* ConditionalNode.canonicalizeConditional (174) *)
  "\<lbrakk>kind g cond = IntegerLessThanNode fb tb;
    stpi_upper (stamp g fb) \<le> stpi_lower (stamp g tb)\<rbrakk>
  \<Longrightarrow> CanonicalizeConditional g (ConditionalNode cond tb fb) (RefNode tb)"

  (* ConditionalNode.canonicalizeConditional (188) skipping for now:
      Currently don't have ZeroExtendNode, IntegerConvertNode *)

  (* ConditionalNode.canonicalizeConditional (213) skipping for now:
      Currently don't have an IntegerTestNode  *)
  
  (* ConditionalNode.canonicalizeConditional (227) skipping for now:
      Currently don't have a RightShiftNode to transform into  *)

  (* ConditionalNode.canonicalizeConditional (253) skipping for now:
      Currently don't have a RoundNode or FloatLessThanNode  *)

inductive CanonicalizeAdd :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  add_both_const:
  "\<lbrakk>kind g x = ConstantNode c_1;
    kind g y = ConstantNode c_2;
    val = intval_add c_1 c_2\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd g (AddNode x y) (ConstantNode val)" |

  add_xzero: (* AddNode.canonical (100) *)
  "\<lbrakk>kind g x = ConstantNode c_1;
    \<not>(is_ConstantNode (kind g y));
    c_1 = (IntVal32 0)\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd g (AddNode x y) (RefNode y)" |

  add_yzero: (* AddNode.canonical (100) *)
  "\<lbrakk>\<not>(is_ConstantNode (kind g x));
    kind g y = ConstantNode c_2;
    c_2 = (IntVal32 0)\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd g (AddNode x y) (RefNode x)" |

  add_xsub:  (* AddNode.canonical (85) *)
  (* (a - y) + y \<Rightarrow> a *)
  "\<lbrakk>kind g x = SubNode a y \<rbrakk> 
    \<Longrightarrow> CanonicalizeAdd g (AddNode x y) (RefNode a)" |

  add_ysub:  (* AddNode.canonical (92) *)
  (* x + (a - x) \<Rightarrow> a *)
  "\<lbrakk>kind g y = SubNode a x \<rbrakk> 
    \<Longrightarrow> CanonicalizeAdd g (AddNode x y) (RefNode a)" |

  (* AddNode.canonical (113) skipping for now:
    No ZeroExtendNode *) 

  add_xnegate:  (* AddNode.canonical (160) *)
  (* (-x + y) \<Rightarrow> (y - x) *)
  "\<lbrakk>kind g nx = NegateNode x \<rbrakk> 
    \<Longrightarrow> CanonicalizeAdd g (AddNode nx y) (SubNode y x)" |

  add_ynegate:  (* AddNode.canonical (165) *)
  (* (x + (-y)) \<Rightarrow> (x - y) *)
  "\<lbrakk>kind g ny = NegateNode y \<rbrakk> 
    \<Longrightarrow> CanonicalizeAdd g (AddNode x ny) (SubNode x y)"

  (* TODO: reassociation of constants *) 

inductive CanonicalizeIf :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool"
  for g where
  trueConst: (* IfNode.simplify (287) *)
  "\<lbrakk>kind g cond = ConstantNode condv;
    val_to_bool condv\<rbrakk>
   \<Longrightarrow> CanonicalizeIf g (IfNode cond tb fb) (RefNode tb)" |

  falseConst: (* IfNode.simplify (287) *)
  "\<lbrakk>kind g cond = ConstantNode condv;
    \<not>(val_to_bool condv)\<rbrakk>
   \<Longrightarrow> CanonicalizeIf g (IfNode cond tb fb) (RefNode fb)" |
  
  eqBranch: (* In ConditionalNode.canonicalizeConditional(152) *)
  "\<lbrakk>\<not>(is_ConstantNode (kind g cond));
    tb = fb\<rbrakk>
   \<Longrightarrow> CanonicalizeIf g (IfNode cond tb fb) (RefNode tb)" |

  (* Brae: made up - find where this occurs *)
  (* KT: I imagine the IntegerEqualsNode x x will get canonicalized to a true ConstantNode first *)
  eqCondition: 
  "\<lbrakk>kind g cond = IntegerEqualsNode x x\<rbrakk>
   \<Longrightarrow> CanonicalizeIf g (IfNode cond tb fb) (RefNode tb)"

inductive CanonicalizeBinaryArithmeticNode :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
 add_const_fold: (* BinaryArithmeticNode.canonical (94) *)
   "\<lbrakk>op = kind g op_id;
    is_AddNode op;
    kind g (ir_x op) = ConditionalNode cond tb fb;
    kind g tb = ConstantNode c_1;
    kind g fb = ConstantNode c_2;
    kind g (ir_y op) = ConstantNode c_3;
    tv = intval_add c_1 c_3;
    fv = intval_add c_2 c_3;
    g' = replace_node tb ((ConstantNode tv), constantAsStamp tv) g;
    g'' = replace_node fb ((ConstantNode fv), constantAsStamp fv) g';
    g''' = replace_node op_id (kind g (ir_x op), meet (constantAsStamp tv) (constantAsStamp fv)) g'' \<rbrakk>
    \<Longrightarrow> CanonicalizeBinaryArithmeticNode op_id g g'''"

  (* TODO: other operators: should these be done as separate rules or should above one be made generic?
     Need to make tradeoff on simplicity to prove vs conciseness/readability? *)

(* TODO: is there a nice way to genericise the below rules for any IRNode that is_BinaryCommutative *)
inductive CanonicalizeCommutativeBinaryArithmeticNode :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool"
  for g where
  (* BinaryArithmeticNode.maybeCommuteInputs *)
  add_ids_ordered:
  "\<lbrakk>\<not>(is_ConstantNode (kind g y));
    ((is_ConstantNode (kind g x)) \<or> (x > y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (AddNode x y) (AddNode y x)" | 

  and_ids_ordered:
  "\<lbrakk>\<not>(is_ConstantNode (kind g y));
    ((is_ConstantNode (kind g x)) \<or> (x > y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (AndNode x y) (AndNode y x)" | 

  int_equals_ids_ordered:
  "\<lbrakk>\<not>(is_ConstantNode (kind g y));
    ((is_ConstantNode (kind g x)) \<or> (x > y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (IntegerEqualsNode x y) (IntegerEqualsNode y x)" | 

  mul_ids_ordered:
  "\<lbrakk>\<not>(is_ConstantNode (kind g y));
    ((is_ConstantNode (kind g x)) \<or> (x > y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (MulNode x y) (MulNode y x)" | 

  or_ids_ordered:
  "\<lbrakk>\<not>(is_ConstantNode (kind g y));
    ((is_ConstantNode (kind g x)) \<or> (x > y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (OrNode x y) (OrNode y x)" | 

  xor_ids_ordered:
  "\<lbrakk>\<not>(is_ConstantNode (kind g y));
    ((is_ConstantNode (kind g x)) \<or> (x > y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (XorNode x y) (XorNode y x)" |

  (* TODO: these swaps to make constants appear as second variable may interact 
    with other canonicalization rules (e.g. for add) that deal with first arguments being constant  *)
  add_swap_const_first:
  "\<lbrakk>is_ConstantNode (kind g x);
    \<not>(is_ConstantNode (kind g y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (AddNode x y) (AddNode y x)" | 

  and_swap_const_first:
  "\<lbrakk>is_ConstantNode (kind g x);
    \<not>(is_ConstantNode (kind g y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (AndNode x y) (AndNode y x)" | 

  int_equals_swap_const_first:
  "\<lbrakk>is_ConstantNode (kind g x);
    \<not>(is_ConstantNode (kind g y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (IntegerEqualsNode x y) (IntegerEqualsNode y x)" | 
  
  mul_swap_const_first:
  "\<lbrakk>is_ConstantNode (kind g x);
    \<not>(is_ConstantNode (kind g y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (MulNode x y) (MulNode y x)" | 

  or_swap_const_first:
  "\<lbrakk>is_ConstantNode (kind g x);
    \<not>(is_ConstantNode (kind g y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (OrNode x y) (OrNode y x)" | 

  xor_swap_const_first:
  "\<lbrakk>is_ConstantNode (kind g x);
    \<not>(is_ConstantNode (kind g y))\<rbrakk>
    \<Longrightarrow> CanonicalizeCommutativeBinaryArithmeticNode g (XorNode x y) (XorNode y x)"


inductive CanonicalizeSub :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool"
  for g where
  sub_same: (* SubNode.canonical(76) *)
  "\<lbrakk>x = y;
    stamp g x = (IntegerStamp b l h)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub g (SubNode x y) (ConstantNode (IntVal32 0))" |

  sub_both_const:
  "\<lbrakk>kind g x = ConstantNode c_1;
    kind g y = ConstantNode c_2;
    val = intval_sub c_1 c_2\<rbrakk>
    \<Longrightarrow> CanonicalizeSub g (SubNode x y) (ConstantNode val)"  |

  sub_left_add1: (* SubNode.canonical(86) *)
  (* (a + b) - b \<Rightarrow> a *)
  "\<lbrakk>kind g left = AddNode a b\<rbrakk> 
    \<Longrightarrow> CanonicalizeSub g (SubNode left b) (RefNode a)" |

  sub_left_add2: (* SubNode.canonical(90) *)
  (* (a + b) - a \<Rightarrow> b *)
  "\<lbrakk>kind g left = AddNode a b\<rbrakk> 
    \<Longrightarrow> CanonicalizeSub g (SubNode left a) (RefNode b)" |

  sub_left_sub: (* SubNode.canonical(94) *)
  (* (a - b) - a \<Rightarrow> (-b) *)
  "\<lbrakk>kind g left = SubNode a b\<rbrakk> 
    \<Longrightarrow> CanonicalizeSub g (SubNode left a) (NegateNode b)" |

  sub_right_add1: (* SubNode.canonical(103) *)
  (* a - (a + b) \<Rightarrow> (-b) *)
  "\<lbrakk>kind g right = AddNode a b\<rbrakk> 
    \<Longrightarrow> CanonicalizeSub g (SubNode a right) (NegateNode b)" |

  sub_right_add2: (* SubNode.canonical(107) *)
  (* b - (a + b) \<Rightarrow> (-a) *)
  "\<lbrakk>kind g right = AddNode a b\<rbrakk> 
    \<Longrightarrow> CanonicalizeSub g (SubNode b right) (NegateNode a)" | 

  sub_right_sub: (* SubNode.canonical(111) *)
  (* a - (a - b) \<Rightarrow> b *)
  "\<lbrakk>kind g right = AddNode a b\<rbrakk> 
    \<Longrightarrow> CanonicalizeSub g (SubNode a right) (RefNode a)" |

  sub_yzero: (* SubNode.canonical(121) *)
  (* x - 0 \<Rightarrow> x *)
  "\<lbrakk>kind g y = ConstantNode (IntVal32 0)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub g (SubNode x y) (RefNode x)" |

  sub_xzero: (* SubNode.canonical(146) *)
  (* 0 - x \<Rightarrow> (-x). Assuming here y is not a float. *)
  "\<lbrakk>kind g x = ConstantNode (IntVal32 0)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub g (SubNode x y) (NegateNode y)" |

  sub_y_negate: (* SubNode.canonical(152) *)
  (* a - (-b) \<Rightarrow> a + b *)           
  "\<lbrakk>kind g nb = NegateNode b\<rbrakk> 
    \<Longrightarrow> CanonicalizeSub g (SubNode a nb) (AddNode a b)" 

  (* TODO: reassociation in SubNode.canonical(119-151) *)
                                              
inductive CanonicalizeMul :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  mul_both_const:
  "\<lbrakk>kind g x = ConstantNode c_1;
    kind g y = ConstantNode c_2;
    val = intval_mul c_1 c_2\<rbrakk>
    \<Longrightarrow> CanonicalizeMul g (MulNode x y) (ConstantNode val)" |

  mul_xzero: (* MulNode.canonical(124) *) 
  "\<lbrakk>kind g x = ConstantNode c_1;
    \<not>(is_ConstantNode (kind g y));
    c_1 = (IntVal32 0)\<rbrakk>
    \<Longrightarrow> CanonicalizeMul g (MulNode x y) (ConstantNode c_1)" |

  mul_yzero: (* MulNode.canonical(124) *) 
  "\<lbrakk>kind g y = ConstantNode c_1;
    \<not>(is_ConstantNode (kind g x));
    c_1 = (IntVal32 0)\<rbrakk>
    \<Longrightarrow> CanonicalizeMul g (MulNode x y) (ConstantNode c_1)" | 

  mul_xone: (* MulNode.canonical(126) *) 
  "\<lbrakk>kind g x = ConstantNode c_1;
    \<not>(is_ConstantNode (kind g y));
    c_1 = (IntVal32 1)\<rbrakk>
    \<Longrightarrow> CanonicalizeMul g (MulNode x y) (RefNode y)" |

  mul_yone:  (* MulNode.canonical(126) *)
  "\<lbrakk>kind g y = ConstantNode c_1;
    \<not>(is_ConstantNode (kind g x));
    c_1 = (IntVal32 1)\<rbrakk>
    \<Longrightarrow> CanonicalizeMul g (MulNode x y) (RefNode x)" |

   mul_xnegate: (* MulNode.canonical(128) *)
  "\<lbrakk>kind g x = ConstantNode c_1;
    \<not>(is_ConstantNode (kind g y));
    c_1 = (IntVal32 (-1))\<rbrakk>
    \<Longrightarrow> CanonicalizeMul g (MulNode x y) (NegateNode y)" |

  mul_ynegate: (* MulNode.canonical(128) *)
  "\<lbrakk>kind g y = ConstantNode c_1;
    \<not>(is_ConstantNode (kind g x));
    c_1 = (IntVal32 (-1))\<rbrakk>
    \<Longrightarrow> CanonicalizeMul g (MulNode x y) (NegateNode x)" 

  (* NOTE: Skipping bit shift optimisations at MulNode.canonical(130) for now *)

  (* TODO: reassociation in SubNode.canonical(119-151) *)

inductive CanonicalizeAbs :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  abs_abs:  (* AbsNode.canonical(78) *)
  "\<lbrakk>kind g x = (AbsNode y)\<rbrakk>
    \<Longrightarrow> CanonicalizeAbs g (AbsNode x) (AbsNode y)" |

  (* Why don't they canonicalize abs(-x) = abs(x) in Graal source code? 
     Let's try add it here and prove it anyway *)
  abs_negate:
  "\<lbrakk>kind g nx = (NegateNode x)\<rbrakk>
    \<Longrightarrow> CanonicalizeAbs g (AbsNode nx) (AbsNode x)" 
  
inductive CanonicalizeNegate :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  negate_const:
  "\<lbrakk>kind g nx = (ConstantNode val);
    val = (IntVal32 v);
    neg_val = intval_sub (IntVal32 0) val \<rbrakk>
    \<Longrightarrow> CanonicalizeNegate g (NegateNode nx) (ConstantNode neg_val)" |

  negate_negate: (* NegateNode.canonical(88) *)
  "\<lbrakk>kind g nx = (NegateNode x)\<rbrakk>
    \<Longrightarrow> CanonicalizeNegate g (NegateNode nx) (RefNode x)" |

  negate_sub: (* NegateNode.canonical(91) *)
  "\<lbrakk>kind g sub = (SubNode x y);
    stamp g sub = (IntegerStamp _ _ _)\<rbrakk>
    \<Longrightarrow> CanonicalizeNegate g (NegateNode sub) (SubNode y x)"

  (* NOTE: negate_rightshift in NegateNode.canonical(91) skipped, no RightShiftNode *)

inductive CanonicalizeNot :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  not_const: (* UnaryArithmeticNode.findSynonym(78) *)
  "\<lbrakk>kind g nx = (ConstantNode val);
    neg_val = intval_not val\<rbrakk>
    \<Longrightarrow> CanonicalizeNot g (NotNode nx) (ConstantNode neg_val)" |

  not_not:  (* NotNode.canonical(75) *)
  "\<lbrakk>kind g nx = (NotNode x)\<rbrakk>
    \<Longrightarrow> CanonicalizeNot g (NotNode nx) (RefNode x)"

inductive CanonicalizeLogicNegation :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  logical_not_const: (* LogicNegationNode.findSynonym(61) *)
  "\<lbrakk>kind g nx = (ConstantNode val);
    neg_val = bool_to_val (\<not>(val_to_bool val))\<rbrakk>
    \<Longrightarrow> CanonicalizeLogicNegation g (LogicNegationNode nx) (ConstantNode neg_val)" |

  logical_not_not:  (* LogicNegationNode.findSynonym(65) *)
  "\<lbrakk>kind g nx = (LogicNegationNode x)\<rbrakk>
    \<Longrightarrow> CanonicalizeLogicNegation g (LogicNegationNode nx) (RefNode x)"

inductive CanonicalizeAnd :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  and_same: (* AndNode.canonical(82) *)
  "\<lbrakk>x = y\<rbrakk>
    \<Longrightarrow> CanonicalizeAnd g (AndNode x y) (RefNode x)" |

  and_xtrue: (* AndNode.canonical(102) *)
  "\<lbrakk>kind g x = ConstantNode val;
    val_to_bool val\<rbrakk>
    \<Longrightarrow> CanonicalizeAnd g (AndNode x y) (RefNode y)" |

  and_ytrue:  (* AndNode.canonical(102) *)
  "\<lbrakk>kind g y = ConstantNode val;
    val_to_bool val\<rbrakk>
    \<Longrightarrow> CanonicalizeAnd g (AndNode x y) (RefNode x)" | 

  and_xfalse:
  "\<lbrakk>kind g x = ConstantNode val;
    \<not>(val_to_bool val)\<rbrakk>
    \<Longrightarrow> CanonicalizeAnd g (AndNode x y) (ConstantNode val)" |

  and_yfalse:
  "\<lbrakk>kind g y = ConstantNode val;
    \<not>(val_to_bool val)\<rbrakk>
    \<Longrightarrow> CanonicalizeAnd g (AndNode x y) (ConstantNode val)" 

  (* Skipping AndNode.canonical(91), no upMask/downMask for stamps yet? *)
  (* Skipping AndNode.canonical(107), no ZeroExtend/SignExtend yet *)

inductive CanonicalizeOr :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  or_same:  (* OrNode.canonical(93) *)
  "\<lbrakk>x = y\<rbrakk>
    \<Longrightarrow> CanonicalizeOr g (OrNode x y) (RefNode x)" |

  or_xtrue: (* OrNode.canonical(113) *)
  "\<lbrakk>kind g x = ConstantNode val;
    val_to_bool val\<rbrakk>
    \<Longrightarrow> CanonicalizeOr g (OrNode x y) (ConstantNode val)" |

  or_ytrue:  (* OrNode.canonical(113) *)
  "\<lbrakk>kind g y = ConstantNode val;
    val_to_bool val\<rbrakk>
    \<Longrightarrow> CanonicalizeOr g (OrNode x y) (ConstantNode val)" | 

  or_xfalse: (* OrNode.canonical(113) *)
  "\<lbrakk>kind g x = ConstantNode val;
    \<not>(val_to_bool val)\<rbrakk>
    \<Longrightarrow> CanonicalizeOr g (OrNode x y) (RefNode y)" |

  or_yfalse: (* OrNode.canonical(113) *)
  "\<lbrakk>kind g y = ConstantNode val;
    \<not>(val_to_bool val)\<rbrakk>
    \<Longrightarrow> CanonicalizeOr g (OrNode x y) (RefNode x)" 

  (* NOTE: Skipping OrNode.canonical(91), no upMask/downMask for stamps yet? *)
  (* NOTE: Skipping OrNode.canonical(107), no ZeroExtend/SignExtend yet *)

inductive CanonicalizeDeMorgansLaw :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  (* OrNode.canonical(120) *)
  (* (!x \<or> !y) \<Rightarrow> !(x \<and> y) *)
  de_morgan_or_to_and:
  "\<lbrakk>kind g nid = OrNode nx ny;
    kind g nx = NotNode x;
    kind g ny = NotNode y;
    new_add_id = nextNid g;
    g' = add_node new_add_id ((AddNode x y), (IntegerStamp 1 0 1)) g;
    g'' = replace_node nid ((NotNode new_add_id), (IntegerStamp 1 0 1)) g'\<rbrakk>
    \<Longrightarrow> CanonicalizeDeMorgansLaw nid g g''" |

  (* AndNode.canonical(119) *)
  (* (!x \<and> !y) \<Rightarrow> !(x \<or> y) *)
  de_morgan_and_to_or:
  "\<lbrakk>kind g nid = AndNode nx ny;
    kind g nx = NotNode x;
    kind g ny = NotNode y;
    new_add_id = nextNid g;
    g' = add_node new_add_id ((OrNode x y), (IntegerStamp 1 0 1)) g;
    g'' = replace_node nid ((NotNode new_add_id), (IntegerStamp 1 0 1)) g'\<rbrakk>
    \<Longrightarrow> CanonicalizeDeMorgansLaw nid g g''" 

inductive CanonicalizeIntegerEquals :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  int_equals_same_node: (* IntegerEqualsNode.canonical(139) *)
  "\<lbrakk>x = y\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals g (IntegerEqualsNode x y) (ConstantNode (IntVal32 1))" |

  int_equals_distinct: (* IntegerEqualsNode.canonical(143) *)
  "\<lbrakk>alwaysDistinct (stamp g x) (stamp g y)\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals g (IntegerEqualsNode x y) (ConstantNode (IntVal32 0))" |

  int_equals_add_first_both_same: (* IntegerEqualsNode.canonical(152) *)
  (* (x+y) == (x+z) \<Rightarrow> (y == z) *)
  "\<lbrakk>kind g left = AddNode x y;
    kind g right = AddNode x z\<rbrakk> 
    \<Longrightarrow> CanonicalizeIntegerEquals g (IntegerEqualsNode left right) (IntegerEqualsNode y z)" |

  int_equals_add_first_second_same: (* IntegerEqualsNode.canonical(156) *)
  (* (x+y) == (z+x) \<Rightarrow> (y == z) *)
  "\<lbrakk>kind g left = AddNode x y;
    kind g right = AddNode z x\<rbrakk> 
    \<Longrightarrow> CanonicalizeIntegerEquals g (IntegerEqualsNode left right) (IntegerEqualsNode y z)" | 

  int_equals_add_second_first_same:  (* IntegerEqualsNode.canonical(160) *)
  (* (y+x) == (x+z) \<Rightarrow> (y == z) *)
  "\<lbrakk>kind g left = AddNode y x;
    kind g right = AddNode x z\<rbrakk> 
    \<Longrightarrow> CanonicalizeIntegerEquals g (IntegerEqualsNode left right) (IntegerEqualsNode y z)" |

  int_equals_add_second_both__same:  (* IntegerEqualsNode.canonical(164) *)
  (* (y+x) == (z+x) \<Rightarrow> (y == z) *)
  "\<lbrakk>kind g left = AddNode y x;
    kind g right = AddNode z x\<rbrakk> 
    \<Longrightarrow> CanonicalizeIntegerEquals g (IntegerEqualsNode left right) (IntegerEqualsNode y z)" |

  int_equals_sub_first_both_same: (* IntegerEqualsNode.canonical(180) *)
  (* (x-y) == (x-z) \<Rightarrow> (y == z) *)
  "\<lbrakk>kind g left = SubNode x y;
    kind g right = SubNode x z\<rbrakk> 
    \<Longrightarrow> CanonicalizeIntegerEquals g (IntegerEqualsNode left right) (IntegerEqualsNode y z)" |

  int_equals_sub_second_both_same: (* IntegerEqualsNode.canonical(184) *)
  (* (y-x) == (z-x) \<Rightarrow> (y == z) *)
  "\<lbrakk>kind g left = SubNode y x;
    kind g right = SubNode z x\<rbrakk> 
    \<Longrightarrow> CanonicalizeIntegerEquals g (IntegerEqualsNode left right) (IntegerEqualsNode y z)" 

  (* NOTE: missing IntegerEqualsNode.canonicalizeSymmetricConstant rules *)

inductive CanonicalizeIntegerEqualsGraph :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  int_equals_rewrite: (* use above rewrite rules if it matches *)
  "\<lbrakk>CanonicalizeIntegerEquals g node node';
    node = kind g nid;
    g' = replace_node nid (node', stamp g nid) g \<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEqualsGraph nid g g'" | 

  (* IntegerEquals.canonical(197) *)
  (* (x+y) == x \<Rightarrow> (y == 0) *)
  int_equals_left_contains_right1:
  "\<lbrakk>kind g nid = IntegerEqualsNode left x;
    kind g left = AddNode x y;
    const_id = nextNid g;
    g' = add_node const_id ((ConstantNode (IntVal32 0)), constantAsStamp (IntVal32 0)) g; 
    g'' = replace_node const_id ((IntegerEqualsNode y const_id), stamp g nid) g'\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEqualsGraph nid g g''" |

  (* IntegerEquals.canonical(200) *)
  (* (x+y) == y \<Rightarrow> (x == 0) *)
  int_equals_left_contains_right2:
  "\<lbrakk>kind g nid = IntegerEqualsNode left y;
    kind g left = AddNode x y;
    const_id = nextNid g;
    g' = add_node const_id ((ConstantNode (IntVal32 0)), constantAsStamp (IntVal32 0)) g; 
    g'' = replace_node const_id ((IntegerEqualsNode x const_id), stamp g nid) g'\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEqualsGraph nid g g''" | 

  (* IntegerEquals.canonical(208) *)
  (* x == (x+y) \<Rightarrow> (y == 0) *)
  int_equals_right_contains_left1:
  "\<lbrakk>kind g nid = IntegerEqualsNode x right;
    kind g right = AddNode x y;
    const_id = nextNid g;
    g' = add_node const_id ((ConstantNode (IntVal32 0)), constantAsStamp (IntVal32 0)) g; 
    g'' = replace_node const_id ((IntegerEqualsNode y const_id), stamp g nid) g'\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEqualsGraph nid g g''" |

  (* IntegerEquals.canonical(211) *)
  (* y == (x+y) \<Rightarrow> (x == 0) *)
  int_equals_right_contains_left2:
  "\<lbrakk>kind g nid = IntegerEqualsNode y right;
    kind g right = AddNode x y;
    const_id = nextNid g;
    g' = add_node const_id ((ConstantNode (IntVal32 0)), constantAsStamp (IntVal32 0)) g; 
    g'' = replace_node const_id ((IntegerEqualsNode x const_id), stamp g nid) g'\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEqualsGraph nid g g''" |

  (* IntegerEquals.canonical(219) *)
  (* (x - y) == x \<Rightarrow> (y == 0) *)
  int_equals_left_contains_right3:
  "\<lbrakk>kind g nid = IntegerEqualsNode left x;
    kind g left = SubNode x y;
    const_id = nextNid g;
    g' = add_node const_id ((ConstantNode (IntVal32 0)), constantAsStamp (IntVal32 0)) g; 
    g'' = replace_node const_id ((IntegerEqualsNode y const_id), stamp g nid) g'\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEqualsGraph nid g g''" |

  (* IntegerEquals.canonical(227) *)
  (* x == (x - y) \<Rightarrow> (y == 0) *)
  int_equals_right_contains_left3:
  "\<lbrakk>kind g nid = IntegerEqualsNode x right;
    kind g right = SubNode x y;
    const_id = nextNid g;
    g' = add_node const_id ((ConstantNode (IntVal32 0)), constantAsStamp (IntVal32 0)) g; 
    g'' = replace_node const_id ((IntegerEqualsNode y const_id), stamp g nid) g'\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEqualsGraph nid g g''"

   (* NOTE: missing IntegerEqualsNode.canonicalizeSymmetricConstant rules *)

(* TODO: BinaryArithmeticNode.reassociateMatchedConstants for all associative nodes *)
(* TODO: BinaryArithmeticNode.reassociateUnmatchedValues *)

(* TODO: XorNode *)
(* TODO: IntegerLessThanNode *)
(* TODO: ShortCircuitOrNode *)
(* TODO: IsNullNode *)

(* TODO: SignedDivNode *)
(* TODO: SignedRemNode *)

(* TODO: (Value)PhiNode *)

(* TODO: LoadFieldNode *)
(* TODO: StoreFieldNode *)

inductive CanonicalizationStep :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool"
  for g where
  ConditionalNode:
  "\<lbrakk>CanonicalizeConditional g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  AddNode:
  "\<lbrakk>CanonicalizeAdd g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  IfNode:
  "\<lbrakk>CanonicalizeIf g node node'\<rbrakk>
    \<Longrightarrow> CanonicalizationStep g node node'" |

  (* TODO: fix
  BinaryArithmaticNode:
  "\<lbrakk>CanonicalizeBinaryArithmeticNode g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'"
  *)

  SubNode:
  "\<lbrakk>CanonicalizeSub g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  MulNode:
  "\<lbrakk>CanonicalizeMul g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  AndNode:
  "\<lbrakk>CanonicalizeAnd g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  OrNode:
  "\<lbrakk>CanonicalizeOr g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  AbsNode:
  "\<lbrakk>CanonicalizeAbs g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  NotNode:
  "\<lbrakk>CanonicalizeNot g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  NegateNode:
  "\<lbrakk>CanonicalizeNegate g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'" |

  LogicNegationNode:
  "\<lbrakk>CanonicalizeLogicNegation g node node'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep g node node'"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeConditional .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeAdd .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeIf .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeSub .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeMul .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeAnd .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeOr .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeAbs .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeNot .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeNegate .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeLogicNegation .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizationStep .


(* dummy analysis *)
type_synonym CanonicalizationAnalysis = "bool option"

fun analyse :: "(ID \<times> Seen \<times> CanonicalizationAnalysis) \<Rightarrow> CanonicalizationAnalysis" where
  "analyse i = None"

inductive CanonicalizationPhase 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> CanonicalizationAnalysis) \<Rightarrow> IRGraph \<Rightarrow> bool" where

  \<comment> \<open>Can do a step and optimise for the current node\<close>
  "\<lbrakk>Step analyse g (nid, seen, i) (Some (nid', seen', i'));
    CanonicalizationStep g (kind g nid) node;
  
    g' = replace_node nid (node, stamp g nid) g;
    
    CanonicalizationPhase g' (nid', seen', i') g''\<rbrakk>
    \<Longrightarrow> CanonicalizationPhase g (nid, seen, i) g''" |

  \<comment> \<open>Can do a step, matches whether optimised or not causing non-determinism
      We need to find a way to negate ConditionalEliminationStep\<close>
  "\<lbrakk>Step analyse g (nid, seen, i) (Some (nid', seen', i'));
    
    CanonicalizationPhase g (nid', seen', i') g'\<rbrakk>
    \<Longrightarrow> CanonicalizationPhase g (nid, seen, i) g'" |

  (* TODO: part of the step? *)
  "\<lbrakk>Step analyse g (nid, seen, i) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    CanonicalizationPhase g (nid', seen', i) g'\<rbrakk>
    \<Longrightarrow> CanonicalizationPhase g (nid, seen, i) g'" |

  (* TODO: part of the step? *)
  "\<lbrakk>Step analyse g (nid, seen, i) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> CanonicalizationPhase g (nid, seen, i) g"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizationPhase .

type_synonym Trace = "IRNode list"
inductive CanonicalizationPhaseWithTrace 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> CanonicalizationAnalysis) \<Rightarrow> IRGraph \<Rightarrow> Trace \<Rightarrow> Trace \<Rightarrow> bool" where

  \<comment> \<open>Can do a step and optimise for the current node\<close>
  "\<lbrakk>Step analyse g (nid, seen, i) (Some (nid', seen', i'));
    CanonicalizationStep g (kind g nid) node;
  
    g' = replace_node nid (node, stamp g nid) g;
    
    CanonicalizationPhaseWithTrace g' (nid', seen', i') g'' (kind g nid # t) t' \<rbrakk>
    \<Longrightarrow> CanonicalizationPhaseWithTrace g (nid, seen, i) g'' t t'" |

  \<comment> \<open>Can do a step, matches whether optimised or not causing non-determinism
      We need to find a way to negate ConditionalEliminationStep\<close>
  "\<lbrakk>Step analyse g (nid, seen, i) (Some (nid', seen', i'));
    
    CanonicalizationPhaseWithTrace g (nid', seen', i') g' (kind g nid # t) t' \<rbrakk>
    \<Longrightarrow> CanonicalizationPhaseWithTrace g (nid, seen, i) g' t t'" |

  (* TODO: part of the step? *)
  "\<lbrakk>Step analyse g (nid, seen, i) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    CanonicalizationPhaseWithTrace g (nid', seen', i) g' (kind g nid # t) t' \<rbrakk>
    \<Longrightarrow> CanonicalizationPhaseWithTrace g (nid, seen, i) g' t t'" |

  (* TODO: part of the step? *)
  "\<lbrakk>Step analyse g (nid, seen, i) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> CanonicalizationPhaseWithTrace g (nid, seen, i) g t t"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CanonicalizationPhaseWithTrace .


end