section \<open>Canonicalization Phase\<close>

theory CanonicalizationTree
  imports
    Semantics.IRTreeEval
begin

(* TODO: these functions below could be made more precise (but complicated)
  by operating on stamps rather than just values, as seen in the op table:
  https://github.com/oracle/graal/blob/fbab70f9d788f997c862bdee186ef1d8e6c435f1/compiler/src/org.graalvm.compiler.core.common/src/org/graalvm/compiler/core/common/type/IntegerStamp.java#L602
*)

(* is_idempotent_binary \<oplus> \<Longrightarrow> x \<oplus> x = x *)(* TODO In Graal? *)
fun is_idempotent_binary :: "IRBinaryOp \<Rightarrow> bool" where
"is_idempotent_binary BinAnd = True" |
"is_idempotent_binary BinOr  = True" |
"is_idempotent_binary _      = False"

(* is_idempotent_unary \<ominus> \<Longrightarrow> \<ominus> \<ominus> x = \<ominus> x *)(* TODO In Graal? *)
fun is_idempotent_unary :: "IRUnaryOp \<Rightarrow> bool" where
"is_idempotent_unary UnaryAbs = True" |
"is_idempotent_unary _ = False"

(* is_self_inverse \<ominus> \<Longrightarrow> \<ominus> \<ominus> x = x *)
fun is_self_inverse :: "IRUnaryOp \<Rightarrow> bool" where
"is_self_inverse UnaryNeg = True" |
"is_self_inverse UnaryNot = True" |
"is_self_inverse UnaryLogicNegation = True" |
"is_self_inverse _ = False"

(* is_neutral (\<oplus>, n) \<Longrightarrow> \<forall> x. x \<oplus> n = x *)
fun is_neutral :: "IRBinaryOp \<Rightarrow> Value \<Rightarrow> bool" where
(* x + 0 = x*)
"is_neutral BinAdd (IntVal32 x) = (x = 0)" |
"is_neutral BinAdd (IntVal64 x) = (x = 0)" |
(* x - 0 = x *)
"is_neutral BinSub (IntVal32 x) = (x = 0)" |
"is_neutral BinSub (IntVal64 x) = (x = 0)" |
(* x * 1 = x*)
"is_neutral BinMul (IntVal32 x) = (x = 1)" |
"is_neutral BinMul (IntVal64 x) = (x = 1)" |
(* x & 1 = x *)(* TODO In Graal? *)
"is_neutral BinAnd (IntVal32 x) = (x = 1)" |
"is_neutral BinAnd (IntVal64 x) = (x = 1)" |
(* x | 0 = x *)(* TODO In Graal? *)
"is_neutral BinOr (IntVal32 x) = (x = 0)" |
"is_neutral BinOr (IntVal64 x) = (x = 0)" |
(* x ^ 0 = x *)(* TODO In Graal? *)
"is_neutral BinXor (IntVal32 x) = (x = 0)" |
"is_neutral BinXor (IntVal64 x) = (x = 0)" |

"is_neutral _ _ = False"

(* is_annihilator (\<oplus>, z) \<Longrightarrow> \<forall> x. x \<oplus> z = z (was know as is_zero)*)
fun is_annihilator :: "IRBinaryOp \<Rightarrow> Value \<Rightarrow> bool" where
(* x * 0 = 0 *)
"is_annihilator BinMul (IntVal32 x) = (x = 0)" |
"is_annihilator BinMul (IntVal64 x) = (x = 0)" |
(* x & 0 = 0 *)(* TODO In Graal? *)
"is_annihilator BinAnd (IntVal32 x) = (x = 0)" |
"is_annihilator BinAnd (IntVal64 x) = (x = 0)" |
(* x | 1 = 1 *)(* TODO In Graal? *)
"is_annihilator BinOr  (IntVal32 x) = (x = 1)" |
"is_annihilator BinOr  (IntVal64 x) = (x = 1)" |

"is_annihilator _ _ = False"

fun int_to_value :: "Value \<Rightarrow> int \<Rightarrow> Value" where
"int_to_value (IntVal32 _) y = (IntVal32 (word_of_int y))" |
"int_to_value (IntVal64 _) y = (IntVal64 (word_of_int y))" |
"int_to_value _ _ = UndefVal"

(* TODO: we should only handle y values being constant and let a higher
    level function swap values (if commutative) and try to recanonicalize if
    x is constant and y is not... (since this is done by almost all binary nodes) *)
inductive CanonicalizeBinaryOp :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  binary_const_fold:
  "\<lbrakk>x = (ConstantExpr val1);
   y = (ConstantExpr val2);
   val = bin_eval op val1 val2;
   val \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) (ConstantExpr val)" |

  binary_fold_yneutral:
  "\<lbrakk>y = (ConstantExpr c);
   is_neutral op c;
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    stp_bits stampx = stp_bits stampy;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy\<rbrakk>
     \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) x" |

  binary_fold_yzero32:
  "\<lbrakk>y = ConstantExpr c;
    is_annihilator op c;
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    stp_bits stampx = stp_bits stampy;
    stp_bits stampx = 32;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) (ConstantExpr c)" |

  binary_fold_yzero64:
  "\<lbrakk>y = ConstantExpr c;
    is_annihilator op c;
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    stp_bits stampx = stp_bits stampy;
    stp_bits stampx = 64;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) (ConstantExpr c)" |

  binary_idempotent: (* Does this need more assumptions? *)
  "\<lbrakk>is_idempotent_binary op\<rbrakk>
    \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x x) x"

inductive CanonicalizeUnaryOp :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  unary_const_fold:
  "\<lbrakk>val' = unary_eval op val;
    val' \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> CanonicalizeUnaryOp (UnaryExpr op (ConstantExpr val)) (ConstantExpr val')"

inductive CanonicalizeMul :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  (* y * (-1) = -y *)
  mul_negate32:
 "\<lbrakk>y = ConstantExpr (IntVal32 (-1));
   stamp_expr x = IntegerStamp 32 lo hi\<rbrakk>
   \<Longrightarrow> CanonicalizeMul (BinaryExpr BinMul x y) (UnaryExpr UnaryNeg x)" |
  mul_negate64:
 "\<lbrakk>y = ConstantExpr (IntVal64 (-1));
   stamp_expr x = IntegerStamp 64 lo hi\<rbrakk>
   \<Longrightarrow> CanonicalizeMul (BinaryExpr BinMul x y) (UnaryExpr UnaryNeg x)"
  (* NOTE: Skipping bit shift optimisations at MulNode.canonical(130) for now *)

inductive CanonicalizeAdd :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
   add_xsub:  (* AddNode.canonical (85) *)
  (* (a - y) + y \<Rightarrow> a *)
  "\<lbrakk>x = (BinaryExpr BinSub a y);
    stampa = stamp_expr a;
    stampy = stamp_expr y;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampy;
    stp_bits stampa = stp_bits stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd (BinaryExpr BinAdd x y) a" |

   add_ysub:  (* AddNode.canonical (92) *)
  (*  x + (a - x) \<Rightarrow> a *)
  "\<lbrakk>y = (BinaryExpr BinSub a x);
    stampa = stamp_expr a;
    stampx = stamp_expr x;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampx;
    stp_bits stampa = stp_bits stampx\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd (BinaryExpr BinAdd x y) a" |

  (* NOTE: skipping AddNode.canonical (113) for now: No ZeroExtendNode currently in IR *)

  add_xnegate:  (* AddNode.canonical (160) *)
  (* (-x + y) \<Rightarrow> (y - x) *)
  "\<lbrakk>nx = (UnaryExpr UnaryNeg x);
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stp_bits stampx = stp_bits stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd (BinaryExpr BinAdd nx y) (BinaryExpr BinSub y x)"  |

  add_ynegate:  (* AddNode.canonical (165) *)
  (* (x + (-y)) \<Rightarrow> (x - y) *)
  "\<lbrakk>ny = (UnaryExpr UnaryNeg y);
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stp_bits stampx = stp_bits stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd (BinaryExpr BinAdd x ny) (BinaryExpr BinSub x y)"

inductive CanonicalizeSub :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  (*
  sub_same: (* SubNode.canonical(76) *)
  (* (x - x) = 0 *)
  "\<lbrakk>stampx = stamp_expr x;
    is_IntegerStamp stampx;
    b = stp_bits stampx;
    zero = (if b = 32 then (IntVal32 0) else (IntVal64 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x x) (ConstantExpr zero)" |
  *)
  sub_same32: (* SubNode.canonical(76) *)
  (* (x - x) = 0 *)
  "\<lbrakk>stampx = stamp_expr x;
    stampx = IntegerStamp 32 lo hi\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x x) (ConstantExpr (IntVal32 0))" |
  sub_same64: (* SubNode.canonical(76) *)
  (* (x - x) = 0 *)
  "\<lbrakk>stampx = stamp_expr x;
    stampx = IntegerStamp 64 lo hi\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x x) (ConstantExpr (IntVal64 0))" |

  sub_left_add1: (* SubNode.canonical(86) *)
  (* (a + b) - b \<Rightarrow> a *)
  "\<lbrakk>x = (BinaryExpr BinAdd a b);
    stampa = stamp_expr a;
    stampb = stamp_expr b;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampb;
    stp_bits stampa = stp_bits stampb\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x b) a" |

  sub_left_add2: (* SubNode.canonical(90) *)
  (* (a + b) - a \<Rightarrow> b *)
  "\<lbrakk>x = (BinaryExpr BinAdd a b);
    stampa = stamp_expr a;
    stampb = stamp_expr b;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampb;
    stp_bits stampa = stp_bits stampb\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x a) b" |

  sub_left_sub: (* SubNode.canonical(94) *)
  (* (a - b) - a \<Rightarrow> (-b) *)
  "\<lbrakk>x = (BinaryExpr BinSub a b);
    stampa = stamp_expr a;
    stampb = stamp_expr b;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampb;
    stp_bits stampa = stp_bits stampb\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x a) (UnaryExpr UnaryNeg b)" |

  sub_right_add1: (* SubNode.canonical(103) *)
  (* a - (a + b) \<Rightarrow> (-b) *)
  "\<lbrakk>y = (BinaryExpr BinAdd a b);
    stampa = stamp_expr a;
    stampb = stamp_expr b;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampb;
    stp_bits stampa = stp_bits stampb\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub a y) (UnaryExpr UnaryNeg b)" |

  sub_right_add2: (* SubNode.canonical(107) *)
  (* b - (a + b) \<Rightarrow> (-a) *)
  "\<lbrakk>y = (BinaryExpr BinAdd a b);
    stampa = stamp_expr a;
    stampb = stamp_expr b;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampb;
    stp_bits stampa = stp_bits stampb\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub b y) (UnaryExpr UnaryNeg a)" |

  sub_right_sub: (* SubNode.canonical(111) *)
  (* a - (a - b) \<Rightarrow> b *)
  "\<lbrakk>y = (BinaryExpr BinSub a b);
    stampa = stamp_expr a;
    stampb = stamp_expr b;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampb;
    stp_bits stampa = stp_bits stampb\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub a y) b" |

  (* SubNode.canonical(146) *)
  (* 0 - x \<Rightarrow> (-x) *)
  sub_xzero32:
  "\<lbrakk>stampx = stamp_expr x;
    stampx = IntegerStamp 32 lo hi\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub (ConstantExpr (IntVal32 0)) x) (UnaryExpr UnaryNeg x)" |
  sub_xzero64:
  "\<lbrakk>stampx = stamp_expr x;
    stampx = IntegerStamp 64 lo hi\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub (ConstantExpr (IntVal64 0)) x) (UnaryExpr UnaryNeg x)" |

  sub_y_negate: (* SubNode.canonical(152) *)
  (* a - (-b) \<Rightarrow> a + b *)
  "\<lbrakk>nb = (UnaryExpr UnaryNeg b);
    stampa = stamp_expr a;
    stampb = stamp_expr b;
    is_IntegerStamp stampa \<and> is_IntegerStamp stampb;
    stp_bits stampa = stp_bits stampb\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub a nb) (BinaryExpr BinAdd a b)"

  (* x - 0 \<Rightarrow> x in SubNode.canonical(121), handled by is_neutral case in CanonicalizeBinaryOp *)

  (* TODO: reassociation in SubNode.canonical(119-151) *)

inductive CanonicalizeNegate :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  negate_negate: (* NegateNode.canonical(88) *)
  (* -(-x) \<Rightarrow> x *)
  "\<lbrakk>nx = (UnaryExpr UnaryNeg x);
    is_IntegerStamp (stamp_expr x)\<rbrakk>
    \<Longrightarrow> CanonicalizeNegate (UnaryExpr UnaryNeg nx) x" |

  negate_sub: (* NegateNode.canonical(91) *)
  (* -(x - y) \<Rightarrow> (y - x) *)
  "\<lbrakk>e = (BinaryExpr BinSub x y);
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stp_bits stampx = stp_bits stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeNegate (UnaryExpr UnaryNeg e) (BinaryExpr BinSub y x)"

inductive CanonicalizeAbs :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  abs_abs:  (* AbsNode.canonical(68) *)
  (* abs(abs(x)) = abs(x) *)
  "\<lbrakk>ax = (UnaryExpr UnaryAbs x);
    is_IntegerStamp (stamp_expr x)\<rbrakk>
    \<Longrightarrow> CanonicalizeAbs (UnaryExpr UnaryAbs ax) ax" |

  abs_neg:  (* AbsNode.canonical(68) *)
  (* abs(-x) = abs(x) *)
  "\<lbrakk>nx = (UnaryExpr UnaryNeg x);
    is_IntegerStamp (stamp_expr x)\<rbrakk>
    \<Longrightarrow> CanonicalizeAbs (UnaryExpr UnaryAbs nx) (UnaryExpr UnaryAbs x)"

inductive CanonicalizeNot :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  not_not: (* NotNode.canonical(75) *)
  (* ~(~x) \<Rightarrow> x *)
  "\<lbrakk>nx = (UnaryExpr UnaryNot x);
    is_IntegerStamp (stamp_expr x)\<rbrakk>
    \<Longrightarrow> CanonicalizeNot (UnaryExpr UnaryNot nx) x"

inductive CanonicalizeAnd :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  and_same: (* AndNode.canonical(82) *)
  (* (x & x) \<Rightarrow> x *)
  "\<lbrakk>is_IntegerStamp (stamp_expr x)\<rbrakk>
    \<Longrightarrow> CanonicalizeAnd (BinaryExpr BinAnd x x) x" |

  and_demorgans: (* AndNode.canonical(119) *)
  (* (~x) & (~y) \<Rightarrow> ~(x | y) *)
  "\<lbrakk>nx = (UnaryExpr UnaryNot x);
    ny = (UnaryExpr UnaryNot y);
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stp_bits stampx = stp_bits stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeAnd (BinaryExpr BinAnd nx ny) (UnaryExpr UnaryNot (BinaryExpr BinOr x y))"

  (* NOTE: Skipping AndNode.canonical(103).... Should be put in CanonicalizeBinaryOp via is_neutral  *)
  (* NOTE: Skipping AndNode.canonical(91), no upMask/downMask for stamps yet? *)
  (* NOTE: Skipping AndNode.canonical(107), no ZeroExtend/SignExtend yet *)

inductive CanonicalizeOr :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  or_same: (* OrNode.canonical(93) *)
  (* (x | x) \<Rightarrow> x *)
  "\<lbrakk>is_IntegerStamp (stamp_expr x)\<rbrakk>
    \<Longrightarrow> CanonicalizeOr (BinaryExpr BinOr x x) x" |

  or_demorgans: (* OrNode.canonical(120) *)
  (* (~x) | (~y) \<Rightarrow> ~(x & y) *)
  "\<lbrakk>nx = (UnaryExpr UnaryNot x);
    ny = (UnaryExpr UnaryNot y);
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stp_bits stampx = stp_bits stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeOr (BinaryExpr BinOr nx ny) (UnaryExpr UnaryNot (BinaryExpr BinAnd x y))"

  (* NOTE: Skipping OrNode.canonical(103). Should be put in CanonicalizeBinaryOp via is_neutral *)
  (* NOTE: Skipping OrNode.canonical(91), no upMask/downMask for stamps yet? *)
  (* NOTE: Skipping OrNode.canonical(107), no ZeroExtend/SignExtend yet *)

inductive CanonicalizeIntegerEquals :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  int_equals_same: (* IntegerEqualsNode.canonical(139) *)
  (* (x == x) \<Rightarrow> T *)
  "\<lbrakk>x = y\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals x y) (ConstantExpr (IntVal32 1))" |

  int_equals_distinct: (* IntegerEqualsNode.canonical(143) *)
  "\<lbrakk>alwaysDistinct (stamp_expr x) (stamp_expr y)\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals x y) (ConstantExpr (IntVal32 0))" |

  int_equals_add_first_both_same: (* IntegerEqualsNode.canonical(152) *)
  (* (x+y) == (x+z) \<Rightarrow> (y == z) *)
  "\<lbrakk>left = (BinaryExpr BinAdd x y);
    right = (BinaryExpr BinAdd x z)\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left right) (BinaryExpr BinIntegerEquals y z)" |

  int_equals_add_first_second_same: (* IntegerEqualsNode.canonical(156) *)
  (* (x+y) == (z+x) \<Rightarrow> (y == z) *)
  "\<lbrakk>left = (BinaryExpr BinAdd x y);
    right = (BinaryExpr BinAdd z x)\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left right) (BinaryExpr BinIntegerEquals y z)" |

  int_equals_add_second_first_same:  (* IntegerEqualsNode.canonical(160) *)
  (* (y+x) == (x+z) \<Rightarrow> (y == z) *)
  "\<lbrakk>left = (BinaryExpr BinAdd y x);
    right = (BinaryExpr BinAdd x z)\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left right) (BinaryExpr BinIntegerEquals y z)" |

  int_equals_add_second_both__same:  (* IntegerEqualsNode.canonical(164) *)
  (* (y+x) == (z+x) \<Rightarrow> (y == z) *)
  "\<lbrakk>left = (BinaryExpr BinAdd y x);
    right = (BinaryExpr BinAdd z x)\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left right) (BinaryExpr BinIntegerEquals y z)" |

  int_equals_sub_first_both_same: (* IntegerEqualsNode.canonical(180) *)
  (* (x-y) == (x-z) \<Rightarrow> (y == z) *)
  "\<lbrakk>left = (BinaryExpr BinSub x y);
    right = (BinaryExpr BinSub x z)\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left right) (BinaryExpr BinIntegerEquals y z)" |

  int_equals_sub_second_both_same: (* IntegerEqualsNode.canonical(184) *)
  (* (y-x) == (z-x) \<Rightarrow> (y == z) *)
  "\<lbrakk>left = (BinaryExpr BinSub y x);
    right = (BinaryExpr BinSub z x)\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left right) (BinaryExpr BinIntegerEquals y z)" |

(* TODO: choosing the bitsize of the zeros below *)

  int_equals_left_contains_right1: (* IntegerEquals.canonical(197) *)
  (* (x+y) == x \<Rightarrow> (y == 0) *)
  "\<lbrakk>left = (BinaryExpr BinAdd x y);
    zero = (ConstantExpr (IntVal32 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left x) (BinaryExpr BinIntegerEquals y zero)" |

  int_equals_left_contains_right2: (* IntegerEqualsNode.canonical(200) *)
  (* (x+y) == y \<Rightarrow> (x == 0) *)
  "\<lbrakk>left = (BinaryExpr BinAdd x y);
    zero = (ConstantExpr (IntVal32 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left y) (BinaryExpr BinIntegerEquals x zero)" |

  int_equals_right_contains_left1: (* IntegerEquals.canonical(208) *)
  (* x == (x+y) \<Rightarrow> (y == 0) *)
  "\<lbrakk>right = (BinaryExpr BinAdd x y);
    zero = (ConstantExpr (IntVal32 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals x right) (BinaryExpr BinIntegerEquals y zero)" |

  int_equals_right_contains_left2: (* IntegerEquals.canonical(211) *)
  (* y == (x+y) \<Rightarrow> (x == 0) *)
  "\<lbrakk>right = (BinaryExpr BinAdd x y);
    zero = (ConstantExpr (IntVal32 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals y right) (BinaryExpr BinIntegerEquals x zero)" |

  int_equals_left_contains_right3: (* IntegerEquals.canonical(219) *)
  (* (x - y) == x \<Rightarrow> (y == 0) *)
  "\<lbrakk>left = (BinaryExpr BinSub x y);
    zero = (ConstantExpr (IntVal32 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals left x) (BinaryExpr BinIntegerEquals y zero)" |

  int_equals_right_contains_left3: (* IntegerEquals.canonical(227) *)
  (* x == (x - y) \<Rightarrow> (y == 0) *)
  "\<lbrakk>right = (BinaryExpr BinSub x y);
    zero = (ConstantExpr (IntVal32 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeIntegerEquals (BinaryExpr BinIntegerEquals x right) (BinaryExpr BinIntegerEquals y zero)"

  (* NOTE: missing IntegerEqualsNode.canonicalizeSymmetricConstant rules *)

inductive CanonicalizeConditional :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  eq_branches:  (* ConditionalNode.canonicalizeConditional (152) *)
  (* c ? x : x \<Rightarrow> x *)
  "\<lbrakk>t = f\<rbrakk>
    \<Longrightarrow> CanonicalizeConditional (ConditionalExpr c t f) t" |

  cond_eq: (* ConditionalNode.canonicalizeConditional (155) *)
  (* (x==y) ? x : y \<Longrightarrow> y *)
  "\<lbrakk>c = (BinaryExpr BinIntegerEquals x y);
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stp_bits stampx = stp_bits stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeConditional (ConditionalExpr c x y) y" |

  condition_bounds_x: (* ConditionalNode.canonicalizeConditional (170) *)
  (* (x < y ? x : y) \<Rightarrow> x    in case we know that x < y via stamps *)
  "\<lbrakk>c = (BinaryExpr BinIntegerLessThan x y);
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    stpi_upper stampx \<le> stpi_lower stampy;
    stp_bits stampx = stp_bits stampy;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeConditional (ConditionalExpr c x y) x" |

  condition_bounds_y: (* ConditionalNode.canonicalizeConditional (175) *)
  (* (x < y ? y : x) \<Rightarrow> y    in case we know that x < y via stamps *)
  "\<lbrakk>c = (BinaryExpr BinIntegerLessThan x y);
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    stpi_upper stampx \<le> stpi_lower stampy;
    stp_bits stampx = stp_bits stampy;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeConditional (ConditionalExpr c y x) y" |

  negate_condition: (* ConditionalNode.findSynonym (284) *)
  (* (\<not>c ? x : y) \<Rightarrow> (c ? y : x) *)
  "\<lbrakk>nc = (UnaryExpr UnaryLogicNegation c);
    stampc = stamp_expr c;
    stampc = IntegerStamp 32 lo hi;
    stampx = stamp_expr x;
    stampy = stamp_expr y;
    stp_bits stampx = stp_bits stampy;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy\<rbrakk>
    \<Longrightarrow> CanonicalizeConditional (ConditionalExpr nc x y) (ConditionalExpr c y x)" |

  const_true:  (* ConditionalNode.findSynonym (286) *)
  (* TRUE ? t : f \<Rightarrow> t *)
  "\<lbrakk>c = ConstantExpr val;
    val_to_bool val\<rbrakk>
    \<Longrightarrow> CanonicalizeConditional (ConditionalExpr c t f) t" |

  const_false:  (* ConditionalNode.findSynonym (288) *)
  (* FALSE ? t : f \<Rightarrow> f*)
  "\<lbrakk>c = ConstantExpr val;
    \<not>(val_to_bool val)\<rbrakk>
    \<Longrightarrow> CanonicalizeConditional (ConditionalExpr c t f) f"

  (* ConditionalNode.canonicalizeConditional (188) skipping for now:
      Currently don't have ZeroExtendNode, IntegerConvertNode *)

  (* ConditionalNode.canonicalizeConditional (213) skipping for now:
      Currently don't have an IntegerTestNode  *)

  (* ConditionalNode.canonicalizeConditional (227) skipping for now:
      Currently don't have a RightShiftNode to transform into  *)

  (* ConditionalNode.canonicalizeConditional (253) skipping for now:
      Currently don't have a RoundNode or FloatLessThanNode  *)

inductive CanonicalizationStep :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  BinaryNode:
  "\<lbrakk>CanonicalizeBinaryOp expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  UnaryNode:
  "\<lbrakk>CanonicalizeUnaryOp expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  NegateNode:
  "\<lbrakk>CanonicalizeNegate expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  NotNode:
  "\<lbrakk>CanonicalizeNegate expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  AddNode:
  "\<lbrakk>CanonicalizeAdd expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  MulNode:
  "\<lbrakk>CanonicalizeMul expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  SubNode:
  "\<lbrakk>CanonicalizeSub expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  AndNode:
  "\<lbrakk>CanonicalizeSub expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  OrNode:
  "\<lbrakk>CanonicalizeSub expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  IntegerEqualsNode:
  "\<lbrakk>CanonicalizeIntegerEquals expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'" |

  ConditionalNode:
  "\<lbrakk>CanonicalizeConditional expr expr'\<rbrakk>
   \<Longrightarrow> CanonicalizationStep expr expr'"

code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeBinaryOp .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeUnaryOp .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeNegate .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeNot .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeAdd .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeSub .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeMul .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeAnd .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeIntegerEquals .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizeConditional .

code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) CanonicalizationStep .

end