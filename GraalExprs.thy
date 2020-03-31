theory GraalExprs
imports Main
begin

(* Stamps are a kind of type system, with a lattice structure. *)
datatype Stamp =
  IntegerStamp |
  FloatStamp
  (* TODO: add other kinds of types *)


section expressions
(*========================================================================
This section takes a 'value-oriented' view of expressions.

It ignores Node IDs, and treats nodes just as values, with
'inputs' that correspond to the Graal IR inputs.
So equality of these nodes is value-based, so roughly corresponds to
the global value numbering equivalence that is done in Graal.
 
The Graal IR 'Node' type is an abstract class with many subclasses.
We define it as a datatype comprised of the *leaf* classes.
If we need to know the set of intermediate abstract classes (like FixedNode or FloatingNode), 
we define those as predicates, named 'isa_<AbstractClassName>(n)'.
========================================================================== *)


(* TODO: could we build up this hierarchy using type classes?
   With this concrete datatype as the instantiation?
*)

datatype IRNode =
  NullNode  (* Not a real node, but used for some return values *)
  | ConstantNode (*String? value*) int
  | ParameterNode (*index*) int
  | AddNode (*x*) IRNode (*y*) IRNode
  | SubNode (*x*) IRNode (*y*) IRNode
  (* and hundreds of other Node subclasses!... *)

(* Next we need some predicates for abstract superclasses. *)
definition isa_BinaryArithmeticNode :: "IRNode \<Rightarrow> bool" where
  "isa_BinaryArithmeticNode node = (\<exists> x y. node = (AddNode x y) \<or> node = (SubNode x y))"

(* ValueNode.isConstant() *)
definition isConstant :: "IRNode \<Rightarrow> bool" where
  "isConstant node = (\<exists> val. node = (ConstantNode val))"



(* These two functions will model our two kinds of edges. *)

(* TODO: type_synonym SuccessorEdges = "IRNode \<Rightarrow> IRNode list" *)
fun inputEdges :: "IRNode \<Rightarrow> IRNode list" where
  "inputEdges (ConstantNode i) = []" |
  "inputEdges (ParameterNode i) = []" |
  "inputEdges (AddNode x y) = [x, y]" |
  "inputEdges (SubNode x y) = [x, y]" |
  "inputEdges Null = []"


(* isAssociative method (only for int expressions at the moment). *)
fun isAssociative :: "IRNode \<Rightarrow> bool" where
  "isAssociative (AddNode x y) = True" |
  "isAssociative (SubNode x y) = True" |
  "isAssociative _ = False"


(* An example expression: (aa + 1) - aa *)
abbreviation eg_aa :: IRNode where
  "eg_aa \<equiv> (ParameterNode 5)"

(* An example of value equivalence of expressions. *)
lemma aa1_eq: "(AddNode eg_aa (ConstantNode 2)) = (AddNode eg_aa (ConstantNode (1+1)))"
  apply(simp)
  done

(* (1 - aa) + aa *)
abbreviation eg_a1a :: IRNode where
  "eg_a1a \<equiv> (AddNode (SubNode (ConstantNode 1) eg_aa) eg_aa)"

lemma expr_a1a_binary [simp]: "isa_BinaryArithmeticNode(eg_a1a)"
  apply(simp add: isa_BinaryArithmeticNode_def)
  done

lemma const_is_constant [simp]: "isConstant(ConstantNode i)"
  apply(simp add: isConstant_def)
  done



section canonical
(*========================================================================
This section is a translation of the 'AddNode/SubNode.canonical' optimizations.

An example goal is to prove that canonical("(aa + 1) - aa)") returns "1".
========================================================================== *)

(* These are partial translations of several Graal expression-optimization methods:
   Limitations: we ignore stamps and views for now, and assume int expressions.
*)

(* From class BinaryArithmeticNode:
    public static <OP> ConstantNode tryConstantFold(BinaryOp<OP> op, ValueNode forX, ValueNode forY, Stamp stamp, NodeView view) {
        if (forX.isConstant() && forY.isConstant()) {
            Constant ret = op.foldConstant(forX.asConstant(), forY.asConstant());
            if (ret != null) {
                return ConstantNode.forPrimitive(stamp, ret);
            }
        }
        return null;
    }
*)

(* Add only.  TODO: take Op (Add/Sub/Mul as a parameter *)
fun BinArithTryConstFold :: "IRNode \<Rightarrow> IRNode \<Rightarrow> Stamp \<Rightarrow> IRNode" where
  "BinArithTryConstFold (ConstantNode a) (ConstantNode b) stamp = ConstantNode (a+b)" |
  "BinArithTryConstFold forX forY stamp = NullNode"


(* From class AddNode:
    private static ValueNode canonical(AddNode addNode, BinaryOp<Add> op, ValueNode forX, ValueNode forY, NodeView view) {
        AddNode self = addNode;
        boolean associative = op.isAssociative();
        if (associative) {
            if (forX instanceof SubNode) {
                SubNode sub = (SubNode) forX;
                if (sub.getY() == forY) {
                    // (a - b) + b
                    return sub.getX();
                }
            }
            if (forY instanceof SubNode) {
                SubNode sub = (SubNode) forY;
                if (sub.getY() == forX) {
                    // b + (a - b)
                    return sub.getX();
                }
            }
        }
    // TODO:
        if (forY.isConstant()) {
            Constant c = forY.asConstant();
            if (op.isNeutral(c)) {
                return forX;
            }
            if (associative && self != null) {
                // canonicalize expressions like "(a + 1) + 2"
                ValueNode reassociated = reassociate(self, ValueNode.isConstantPredicate(), forX, forY, view);
                if (reassociated != self) {
                    return reassociated;
                }
            }
            /* ignore optimisation of extend nodes between two adds ... */
            }
        }
        if (forX instanceof NegateNode) {
            return BinaryArithmeticNode.sub(forY, ((NegateNode) forX).getValue(), view);
        } else if (forY instanceof NegateNode) {
            return BinaryArithmeticNode.sub(forX, ((NegateNode) forY).getValue(), view);
        }
        if (self == null) {
            self = (AddNode) new AddNode(forX, forY).maybeCommuteInputs();
        }
        return self;
    }
*)

(* TODO: only apply first two rules if op is associative. *)

(* PROBLEM: proving the function side-conditions. *)
function AddNodeCanonical :: "IRNode \<Rightarrow> IRNode" where
  "AddNodeCanonical (AddNode (SubNode a b) b) = a" |   (*  (a - b) + b  *)
  "AddNodeCanonical (AddNode b (SubNode a b)) = a" |   (*  b + (a - b)  *)
  "AddNodeCanonical (AddNode a b) = (AddNode a b)"
    if "a \<noteq> (SubNode _ b) \<and> b \<noteq> (SubNode _ a)" 
  apply(auto)


(* From class AddNode:
    public static ValueNode create(ValueNode x, ValueNode y, NodeView view) {
        BinaryOp<Add> op = ArithmeticOpTable.forStamp(x.stamp(view)).getAdd();
        Stamp stamp = op.foldStamp(x.stamp(view), y.stamp(view));
        ConstantNode tryConstantFold = tryConstantFold(op, x, y, stamp, view);
        if (tryConstantFold != null) {
            return tryConstantFold;
        }
        if (x.isConstant() && !y.isConstant()) {
            return canonical(null, op, y, x, view);
        } else {
            return canonical(null, op, x, y, view);
        }
    }
*)


function AddNodeCreate :: "IRNode \<Rightarrow> IRNode \<Rightarrow> IRNode" where
  "AddNodeCreate x y = BinArithTryConstFold x y IntegerStamp"
if "BinArithTryConstFold x y IntegerStamp \<noteq> NullNode" |
  "AddNodeCreate x y = AddNodeCanonical y x"
if "BinArithTryConstFold x y IntegerStamp = NullNode \<and> isConstant x \<and> \<not> isConstant y" |
  "AddNodeCreate x y = AddNodeCanonical x y"
if "BinArithTryConstFold x y IntegerStamp = NullNode \<and> (\<not> isConstant x \<or> isConstant y)"
  apply(auto)
  by fastforce



(*  An example optimization.  *)
theorem canon_a1a: "AddNodeCanonical eg_a1a = (ConstantNode 1)"
  apply(simp)


end
