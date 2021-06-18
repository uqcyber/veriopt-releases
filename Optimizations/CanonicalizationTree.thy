section \<open>Canonicalization Phase\<close>

theory CanonicalizationTree
  imports
    Semantics.IRTreeEval
    Proofs.IRGraphFrames
    Proofs.Stuttering
    Proofs.Bisimulation
    Proofs.Form
    Graph.Traversal
begin

(* TODO: these functions below could be made more precise (but complicated)
  by operating on stamps rather than just values, as seen in the op table:
  https://github.com/oracle/graal/blob/fbab70f9d788f997c862bdee186ef1d8e6c435f1/compiler/src/org.graalvm.compiler.core.common/src/org/graalvm/compiler/core/common/type/IntegerStamp.java#L602
*)

fun is_neutral :: "IRBinaryOp \<Rightarrow> Value \<Rightarrow> bool" where
"is_neutral BinMul (IntVal32 x) = (sint (x) = 1)" |
"is_neutral BinMul (IntVal64 x) = (sint (x) = 1)" |

"is_neutral BinAdd (IntVal32 x) = (sint (x) = 0)" |
"is_neutral BinAdd (IntVal64 x) = (sint (x) = 0)" |

"is_neutral _ _ = False"


fun is_zero :: "IRBinaryOp \<Rightarrow> Value \<Rightarrow> bool" where
"is_zero BinMul (IntVal32 x) = (sint (x) = 0)" |
"is_zero BinMul (IntVal64 x) = (sint (x) = 0)" |
"is_zero _ _ = False"

fun int_to_value :: "Value \<Rightarrow> int \<Rightarrow> Value" where
"int_to_value (IntVal32 _) y = (IntVal32 (word_of_int y))" |
"int_to_value (IntVal64 _) y = (IntVal64 (word_of_int y))" |
"int_to_value _ _ = UndefVal"

(* TODO: we should only handle y values being constant and let a higher
    level function swap values and try to recanonicalize if
    x is constant and y is not... (since this is done by almost all binary nodes) *)

inductive CanonicalizeBinaryOp :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
(*
  swap_binop:
  "\<lbrakk>is_ConstantExpr x;
    \<not>(is_ConstantExpr y);
    CanonicalizeBinaryOp (BinaryExpr op y x) swapped_canonicalize;
    canon =
      (if (swapped_canonicalize = (BinaryExpr op x y)) then
        (BinaryExpr op y x)
      else
        swapped_canonicalize)\<rbrakk>
    \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) canon" |

(*TODO: doesnt work *)
   "\<lbrakk>is_ConstantExpr x;
    \<not>(is_ConstantExpr y);
    \<nexists> k. (CanonicalizeBinaryOp (BinaryExpr op y x) k)\<rbrakk>
    \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) (BinaryExpr op y x)"
*)

  const_fold:
  "\<lbrakk>x = (ConstantExpr val1);
    y = (ConstantExpr val2);
    val = bin_eval op val1 val2\<rbrakk>
    \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) (ConstantExpr val)" |

  fold_yneutral:
 "\<lbrakk>y = (ConstantExpr c);
  is_neutral op c\<rbrakk>
   \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) x" |

  fold_yzero:
 "\<lbrakk>y = ConstantExpr c;
   is_zero op c;
   zero = (int_to_value c (int 0))\<rbrakk>
   \<Longrightarrow> CanonicalizeBinaryOp (BinaryExpr op x y) (ConstantExpr zero)"


inductive CanonicalizeMul :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  mul_negate:
 "\<lbrakk>y = ConstantExpr c;
   c = (IntVal32 (-1)) \<or> c = (IntVal64 (-1))\<rbrakk>
   \<Longrightarrow> CanonicalizeMul (BinaryExpr BinMul x y) (UnaryExpr UnaryNeg x)"

  (* NOTE: Skipping bit shift optimisations at MulNode.canonical(130) for now *)

inductive CanonicalizeAdd :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
   add_xsub:  (* AddNode.canonical (85) *)
  (* (a - y) + y \<Rightarrow> a *)
  "\<lbrakk>x = (BinaryExpr BinSub a y)\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd (BinaryExpr BinAdd x y) a" |

   add_ysub:  (* AddNode.canonical (92) *)
  (*  x + (a - x) \<Rightarrow> a *)
  "\<lbrakk>y = (BinaryExpr BinSub a x)\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd (BinaryExpr BinAdd x y) a" |

  (* NOTE: skipping AddNode.canonical (113) for now: No ZeroExtendNode currently in IR *)

  add_xnegate:  (* AddNode.canonical (160) *)
  (* (-x + y) \<Rightarrow> (y - x) *)
  "\<lbrakk>nx = (UnaryExpr UnaryNeg x)\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd (BinaryExpr BinAdd nx y) (BinaryExpr BinSub y x)"  |

  add_ynegate:  (* AddNode.canonical (165) *)
  (* (x + (-y)) \<Rightarrow> (x - y) *)
  "\<lbrakk>ny = (UnaryExpr UnaryNeg y)\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd (BinaryExpr BinAdd x ny) (BinaryExpr BinSub x y)"

inductive CanonicalizeSub :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  sub_same: (* SubNode.canonical(76) *)
  (* (x - x) = 0 *)
  (* TODO: how to choose int32/int64 here ?*)
  "\<lbrakk>x = y\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x y) (ConstantExpr (IntVal32 0))" |

  sub_left_add1: (* SubNode.canonical(86) *)
  (* (a + b) - b \<Rightarrow> a *)
  "\<lbrakk>x = (BinaryExpr BinAdd a b)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x b) a" |

  sub_left_add2: (* SubNode.canonical(90) *)
  (* (a + b) - a \<Rightarrow> b *)
  "\<lbrakk>x = (BinaryExpr BinAdd a b)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x a) b" |

  sub_left_sub: (* SubNode.canonical(94) *)
  (* (a - b) - a \<Rightarrow> (-b) *)
  "\<lbrakk>x = (BinaryExpr BinSub a b)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x a) (UnaryExpr UnaryNeg b)" |

  sub_right_add1: (* SubNode.canonical(103) *)
  (* a - (a + b) \<Rightarrow> (-b) *)
  "\<lbrakk>y = (BinaryExpr BinAdd a b)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub a y) (UnaryExpr UnaryNeg b)" |

  sub_right_add2: (* SubNode.canonical(107) *)
  (* b - (a + b) \<Rightarrow> (-a) *)
  "\<lbrakk>y = (BinaryExpr BinAdd a b)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub b y) (UnaryExpr UnaryNeg a)" |

  sub_right_sub: (* SubNode.canonical(111) *)
  (* a - (a - b) \<Rightarrow> b *)
  "\<lbrakk>y = (BinaryExpr BinSub a b)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub a y) b" |

  (* TODO: is there a better way to do this without duplicating for 32 and 64 bit? *)

  sub_yzero32: (* SubNode.canonical(121) *)
  (* x - 0 \<Rightarrow> x *)
  "\<lbrakk>y = (ConstantExpr (IntVal32 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x y) x" |
  sub_yzero64: (* SubNode.canonical(121) *)
  (* x - 0 \<Rightarrow> x *)
  "\<lbrakk>y = (ConstantExpr (IntVal64 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub x y) x" |

  sub_xzero32: (* SubNode.canonical(146) *)
  (* 0 - x \<Rightarrow> (-x) *)
  "\<lbrakk>z = (ConstantExpr (IntVal32 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub z x) (UnaryExpr UnaryNeg x)" |
  sub_xzero64: (* SubNode.canonical(146) *)
  (* 0 - x \<Rightarrow> (-x) *)
  "\<lbrakk>z = (ConstantExpr (IntVal64 0))\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub z x) (UnaryExpr UnaryNeg x)" |

  sub_y_negate: (* SubNode.canonical(152) *)
  (* a - (-b) \<Rightarrow> a + b *)
  "\<lbrakk>nb = (UnaryExpr UnaryNeg b)\<rbrakk>
    \<Longrightarrow> CanonicalizeSub (BinaryExpr BinSub a nb) (BinaryExpr BinAdd a b)"

  (* TODO: reassociation in SubNode.canonical(119-151) *)

end