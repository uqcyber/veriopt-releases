object Compiler {

  abstract sealed class nat
  final case class zero_nat() extends nat
  final case class Suc(a: nat) extends nat

  def equal_nata(x0: nat, x1: nat): Boolean = (x0, x1) match {
    case (zero_nat(), Suc(x2)) => false
    case (Suc(x2), zero_nat()) => false
    case (Suc(x2), Suc(y2)) => equal_nata(x2, y2)
    case (zero_nat(), zero_nat()) => true
  }

  trait equal[A] {
    val `Compiler.equal`: (A, A) => Boolean
  }
  def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
    A.`Compiler.equal`(a, b)
  object equal {
    implicit def `Compiler.equal_unit`: equal[Unit] = new equal[Unit] {
      val `Compiler.equal` = (a: Unit, b: Unit) => equal_unita(a, b)
    }
    implicit def `Compiler.equal_nat`: equal[nat] = new equal[nat] {
      val `Compiler.equal` = (a: nat, b: nat) => equal_nata(a, b)
    }
  }

  def equal_unita(u: Unit, v: Unit): Boolean = true

  abstract sealed class num
  final case class One() extends num
  final case class Bit0(a: num) extends num
  final case class Bit1(a: num) extends num

  abstract sealed class int
  final case class zero_int() extends int
  final case class Pos(a: num) extends int
  final case class Neg(a: num) extends int

  abstract sealed class set[A]
  final case class seta[A](a: List[A]) extends set[A]
  final case class coset[A](a: List[A]) extends set[A]

  abstract sealed class char
  final case class
  Char(a: Boolean, b: Boolean, c: Boolean, d: Boolean, e: Boolean, f: Boolean,
       g: Boolean, h: Boolean)
    extends char

  abstract sealed class pred[A]
  final case class Seq[A](a: Unit => seq[A]) extends pred[A]

  abstract sealed class seq[A]
  final case class Empty[A]() extends seq[A]
  final case class Insert[A](a: A, b: pred[A]) extends seq[A]
  final case class Join[A](a: pred[A], b: seq[A]) extends seq[A]

  abstract sealed class IRNode
  final case class CallNode() extends IRNode
  final case class ConstantNode(a: int) extends IRNode
  final case class ParameterNode(a: int) extends IRNode
  final case class PhiNode() extends IRNode
  final case class AddNode() extends IRNode
  final case class SubNode() extends IRNode
  final case class MulNode() extends IRNode
  final case class SwitchNode() extends IRNode
  final case class IfNode() extends IRNode
  final case class ShortCircuitOrNode(a: Boolean, b: Boolean) extends IRNode
  final case class LogicNegationNode() extends IRNode
  final case class KillingBeginNode() extends IRNode
  final case class BeginNode() extends IRNode
  final case class StartNode() extends IRNode
  final case class LoopEndNode() extends IRNode
  final case class MergeNode() extends IRNode
  final case class ReturnNode() extends IRNode
  final case class EndNode() extends IRNode
  final case class LoopBeginNode() extends IRNode
  final case class LoopExit() extends IRNode
  final case class AbsNode() extends IRNode
  final case class AndNode() extends IRNode
  final case class OrNode() extends IRNode
  final case class XorNode() extends IRNode
  final case class NegateNode() extends IRNode
  final case class IntegerEqualsNode() extends IRNode
  final case class IntegerLessThanNode() extends IRNode
  final case class ConditionalNode() extends IRNode
  final case class NewInstanceNode(a: List[char]) extends IRNode
  final case class LoadFieldNode(a: List[char]) extends IRNode
  final case class StoreFieldNode(a: List[char]) extends IRNode
  final case class LoadStaticFieldNode(a: List[char], b: List[char]) extends
    IRNode
  final case class StoreStaticFieldNode(a: List[char], b: List[char]) extends
    IRNode
  final case class FrameStateNode() extends IRNode

  abstract sealed class IRGraph
  final case class
  Graph(a: set[nat], b: nat => IRNode, c: nat => List[nat], d: nat => List[nat])
    extends IRGraph

  abstract sealed class Value
  final case class UndefVal() extends Value
  final case class IntVal(a: int) extends Value

  abstract sealed class EvalState
  final case class
  EvalStatea(a: IRGraph, b: nat => Value, c: List[Value],
             d: (List[char]) => Value,
             e: nat => Option[(List[char]) => Option[Value]], f: nat => nat)
    extends EvalState

  def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

  def dup(x0: int): int = x0 match {
    case Neg(n) => Neg(Bit0(n))
    case Pos(n) => Pos(Bit0(n))
    case zero_int() => zero_int()
  }

  def uminus_int(x0: int): int = x0 match {
    case Neg(m) => Pos(m)
    case Pos(m) => Neg(m)
    case zero_int() => zero_int()
  }

  def plus_num(x0: num, x1: num): num = (x0, x1) match {
    case (Bit1(m), Bit1(n)) => Bit0(plus_num(plus_num(m, n), One()))
    case (Bit1(m), Bit0(n)) => Bit1(plus_num(m, n))
    case (Bit1(m), One()) => Bit0(plus_num(m, One()))
    case (Bit0(m), Bit1(n)) => Bit1(plus_num(m, n))
    case (Bit0(m), Bit0(n)) => Bit0(plus_num(m, n))
    case (Bit0(m), One()) => Bit1(m)
    case (One(), Bit1(n)) => Bit0(plus_num(n, One()))
    case (One(), Bit0(n)) => Bit1(n)
    case (One(), One()) => Bit0(One())
  }

  def one_int: int = Pos(One())

  def BitM(x0: num): num = x0 match {
    case One() => One()
    case Bit0(n) => Bit1(BitM(n))
    case Bit1(n) => Bit1(Bit0(n))
  }

  def minus_int(k: int, l: int): int = (k, l) match {
    case (Neg(m), Neg(n)) => sub(n, m)
    case (Neg(m), Pos(n)) => Neg(plus_num(m, n))
    case (Pos(m), Neg(n)) => Pos(plus_num(m, n))
    case (Pos(m), Pos(n)) => sub(m, n)
    case (zero_int(), l) => uminus_int(l)
    case (k, zero_int()) => k
  }

  def plus_int(k: int, l: int): int = (k, l) match {
    case (Neg(m), Neg(n)) => Neg(plus_num(m, n))
    case (Neg(m), Pos(n)) => sub(n, m)
    case (Pos(m), Neg(n)) => sub(m, n)
    case (Pos(m), Pos(n)) => Pos(plus_num(m, n))
    case (zero_int(), l) => l
    case (k, zero_int()) => k
  }

  def sub(x0: num, x1: num): int = (x0, x1) match {
    case (Bit0(m), Bit1(n)) => minus_int(dup(sub(m, n)), one_int)
    case (Bit1(m), Bit0(n)) => plus_int(dup(sub(m, n)), one_int)
    case (Bit1(m), Bit1(n)) => dup(sub(m, n))
    case (Bit0(m), Bit0(n)) => dup(sub(m, n))
    case (One(), Bit1(n)) => Neg(Bit0(n))
    case (One(), Bit0(n)) => Neg(BitM(n))
    case (Bit1(m), One()) => Pos(Bit0(m))
    case (Bit0(m), One()) => Pos(BitM(m))
    case (One(), One()) => zero_int()
  }

  def nth[A](x0: List[A], x1: nat): A = (x0, x1) match {
    case (x :: xs, Suc(n)) => nth[A](xs, n)
    case (x :: xs, zero_nat()) => x
  }

  def filtera[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
    case (p, Nil) => Nil
    case (p, x :: xs) => (if (p(x)) x :: filtera[A](p, xs) else filtera[A](p, xs))
  }

  def filter[A](p: A => Boolean, x1: set[A]): set[A] = (p, x1) match {
    case (p, seta(xs)) => seta[A](filtera[A](p, xs))
  }

  def member[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
    case (Nil, y) => false
    case (x :: xs, y) => eq[A](x, y) || member[A](xs, y)
  }

  def the_elem[A](x0: set[A]): A = x0 match {
    case seta(List(x)) => x
  }

  def applya[A, B](f: A => pred[B], x1: seq[A]): seq[B] = (f, x1) match {
    case (f, Empty()) => Empty[B]()
    case (f, Insert(x, p)) => Join[B](f(x), Join[B](bind[A, B](p, f), Empty[B]()))
    case (f, Join(p, xq)) => Join[B](bind[A, B](p, f), applya[A, B](f, xq))
  }

  def bind[A, B](x0: pred[A], f: A => pred[B]): pred[B] = (x0, f) match {
    case (Seq(g), f) => Seq[B](((_: Unit) => applya[A, B](f, g(()))))
  }

  def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
    case (n, x :: xs) => gen_length[A](Suc(n), xs)
    case (n, Nil) => n
  }

  def membera[A : equal](xa0: seq[A], x: A): Boolean = (xa0, x) match {
    case (Empty(), x) => false
    case (Insert(y, p), x) => eq[A](x, y) || (eval[A](p)).apply(x)
    case (Join(p, xq), x) => (eval[A](p)).apply(x) || membera[A](xq, x)
  }

  def eval[A : equal](x0: pred[A]): A => Boolean = x0 match {
    case Seq(f) => ((a: A) => membera[A](f(()), a))
  }

  def holds(p: pred[Unit]): Boolean = (eval[Unit](p)).apply(())

  def bot_pred[A]: pred[A] = Seq[A](((_: Unit) => Empty[A]()))

  def single[A](x: A): pred[A] = Seq[A](((_: Unit) => Insert[A](x, bot_pred[A])))

  def sup_pred[A](x0: pred[A], x1: pred[A]): pred[A] = (x0, x1) match {
    case (Seq(f), Seq(g)) =>
      Seq[A](((_: Unit) =>
        (f(()) match {
          case Empty() => g(())
          case Insert(x, p) => Insert[A](x, sup_pred[A](p, Seq[A](g)))
          case Join(p, xq) => adjunct[A](Seq[A](g), Join[A](p, xq))
        })))
  }

  def adjunct[A](p: pred[A], x1: seq[A]): seq[A] = (p, x1) match {
    case (p, Empty()) => Join[A](p, Empty[A]())
    case (p, Insert(x, q)) => Insert[A](x, sup_pred[A](q, p))
    case (p, Join(q, xq)) => Join[A](q, adjunct[A](p, xq))
  }

  def if_pred(b: Boolean): pred[Unit] =
    (if (b) single[Unit](()) else bot_pred[Unit])

  def equal_num(x0: num, x1: num): Boolean = (x0, x1) match {
    case (Bit0(x2), Bit1(x3)) => false
    case (Bit1(x3), Bit0(x2)) => false
    case (One(), Bit1(x3)) => false
    case (Bit1(x3), One()) => false
    case (One(), Bit0(x2)) => false
    case (Bit0(x2), One()) => false
    case (Bit1(x3), Bit1(y3)) => equal_num(x3, y3)
    case (Bit0(x2), Bit0(y2)) => equal_num(x2, y2)
    case (One(), One()) => true
  }

  def equal_int(x0: int, x1: int): Boolean = (x0, x1) match {
    case (Neg(k), Neg(l)) => equal_num(k, l)
    case (Neg(k), Pos(l)) => false
    case (Neg(k), zero_int()) => false
    case (Pos(k), Neg(l)) => false
    case (Pos(k), Pos(l)) => equal_num(k, l)
    case (Pos(k), zero_int()) => false
    case (zero_int(), Neg(l)) => false
    case (zero_int(), Pos(l)) => false
    case (zero_int(), zero_int()) => true
  }

  def equal_Value(x0: Value, x1: Value): Boolean = (x0, x1) match {
    case (UndefVal(), IntVal(x2)) => false
    case (IntVal(x2), UndefVal()) => false
    case (IntVal(x2), IntVal(y2)) => equal_int(x2, y2)
    case (UndefVal(), UndefVal()) => true
  }

  def is_binary_node(x0: IRNode): Boolean = x0 match {
    case AddNode() => true
    case SubNode() => true
    case MulNode() => true
    case AndNode() => true
    case OrNode() => true
    case XorNode() => true
    case CallNode() => false
    case ConstantNode(v) => false
    case ParameterNode(v) => false
    case PhiNode() => false
    case SwitchNode() => false
    case IfNode() => false
    case ShortCircuitOrNode(v, va) => false
    case LogicNegationNode() => false
    case KillingBeginNode() => false
    case BeginNode() => false
    case StartNode() => false
    case LoopEndNode() => false
    case MergeNode() => false
    case ReturnNode() => false
    case EndNode() => false
    case LoopBeginNode() => false
    case LoopExit() => false
    case AbsNode() => false
    case NegateNode() => false
    case IntegerEqualsNode() => false
    case IntegerLessThanNode() => false
    case ConditionalNode() => false
    case NewInstanceNode(v) => false
    case LoadFieldNode(v) => false
    case StoreFieldNode(v) => false
    case LoadStaticFieldNode(v, va) => false
    case StoreStaticFieldNode(v, va) => false
    case FrameStateNode() => false
  }

  def is_unary_node(x0: IRNode): Boolean = x0 match {
    case AbsNode() => true
    case NegateNode() => true
    case CallNode() => false
    case ConstantNode(v) => false
    case ParameterNode(v) => false
    case PhiNode() => false
    case AddNode() => false
    case SubNode() => false
    case MulNode() => false
    case SwitchNode() => false
    case IfNode() => false
    case ShortCircuitOrNode(v, va) => false
    case LogicNegationNode() => false
    case KillingBeginNode() => false
    case BeginNode() => false
    case StartNode() => false
    case LoopEndNode() => false
    case MergeNode() => false
    case ReturnNode() => false
    case EndNode() => false
    case LoopBeginNode() => false
    case LoopExit() => false
    case AndNode() => false
    case OrNode() => false
    case XorNode() => false
    case IntegerEqualsNode() => false
    case IntegerLessThanNode() => false
    case ConditionalNode() => false
    case NewInstanceNode(v) => false
    case LoadFieldNode(v) => false
    case StoreFieldNode(v) => false
    case LoadStaticFieldNode(v, va) => false
    case StoreStaticFieldNode(v, va) => false
    case FrameStateNode() => false
  }

  def val_to_bool(x0: Value): Boolean = x0 match {
    case IntVal(x) => (if (equal_int(x, zero_int())) false else true)
    case UndefVal() => false
  }

  def bool_to_val(x0: Boolean): Value = x0 match {
    case true => IntVal(one_int)
    case false => IntVal(zero_int())
  }

  def binary_bool_expr(xa0: IRNode, x: Boolean, y: Boolean): Value = (xa0, x, y)
  match {
    case (AndNode(), x, y) => bool_to_val(x && y)
    case (OrNode(), x, y) => bool_to_val(x || y)
    case (XorNode(), x, y) => bool_to_val((x || y) && ! (x && y))
    case (CallNode(), uv, uw) => UndefVal()
    case (ConstantNode(v), uv, uw) => UndefVal()
    case (ParameterNode(v), uv, uw) => UndefVal()
    case (PhiNode(), uv, uw) => UndefVal()
    case (AddNode(), uv, uw) => UndefVal()
    case (SubNode(), uv, uw) => UndefVal()
    case (MulNode(), uv, uw) => UndefVal()
    case (SwitchNode(), uv, uw) => UndefVal()
    case (IfNode(), uv, uw) => UndefVal()
    case (ShortCircuitOrNode(v, va), uv, uw) => UndefVal()
    case (LogicNegationNode(), uv, uw) => UndefVal()
    case (KillingBeginNode(), uv, uw) => UndefVal()
    case (BeginNode(), uv, uw) => UndefVal()
    case (StartNode(), uv, uw) => UndefVal()
    case (LoopEndNode(), uv, uw) => UndefVal()
    case (MergeNode(), uv, uw) => UndefVal()
    case (ReturnNode(), uv, uw) => UndefVal()
    case (EndNode(), uv, uw) => UndefVal()
    case (LoopBeginNode(), uv, uw) => UndefVal()
    case (LoopExit(), uv, uw) => UndefVal()
    case (AbsNode(), uv, uw) => UndefVal()
    case (NegateNode(), uv, uw) => UndefVal()
    case (IntegerEqualsNode(), uv, uw) => UndefVal()
    case (IntegerLessThanNode(), uv, uw) => UndefVal()
    case (ConditionalNode(), uv, uw) => UndefVal()
    case (NewInstanceNode(v), uv, uw) => UndefVal()
    case (LoadFieldNode(v), uv, uw) => UndefVal()
    case (StoreFieldNode(v), uv, uw) => UndefVal()
    case (LoadStaticFieldNode(v, va), uv, uw) => UndefVal()
    case (StoreStaticFieldNode(v, va), uv, uw) => UndefVal()
    case (FrameStateNode(), uv, uw) => UndefVal()
  }

  def times_num(m: num, n: num): num = (m, n) match {
    case (Bit1(m), Bit1(n)) =>
      Bit1(plus_num(plus_num(m, n), Bit0(times_num(m, n))))
    case (Bit1(m), Bit0(n)) => Bit0(times_num(Bit1(m), n))
    case (Bit0(m), Bit1(n)) => Bit0(times_num(m, Bit1(n)))
    case (Bit0(m), Bit0(n)) => Bit0(Bit0(times_num(m, n)))
    case (One(), n) => n
    case (m, One()) => m
  }

  def times_int(k: int, l: int): int = (k, l) match {
    case (Neg(m), Neg(n)) => Pos(times_num(m, n))
    case (Neg(m), Pos(n)) => Neg(times_num(m, n))
    case (Pos(m), Neg(n)) => Neg(times_num(m, n))
    case (Pos(m), Pos(n)) => Pos(times_num(m, n))
    case (zero_int(), l) => zero_int()
    case (k, zero_int()) => zero_int()
  }

  def less_eq_num(x0: num, n: num): Boolean = (x0, n) match {
    case (Bit1(m), Bit0(n)) => less_num(m, n)
    case (Bit1(m), Bit1(n)) => less_eq_num(m, n)
    case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
    case (Bit0(m), Bit0(n)) => less_eq_num(m, n)
    case (Bit1(m), One()) => false
    case (Bit0(m), One()) => false
    case (One(), n) => true
  }

  def less_num(m: num, x1: num): Boolean = (m, x1) match {
    case (Bit1(m), Bit0(n)) => less_num(m, n)
    case (Bit1(m), Bit1(n)) => less_num(m, n)
    case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
    case (Bit0(m), Bit0(n)) => less_num(m, n)
    case (One(), Bit1(n)) => true
    case (One(), Bit0(n)) => true
    case (m, One()) => false
  }

  def less_int(x0: int, x1: int): Boolean = (x0, x1) match {
    case (Neg(k), Neg(l)) => less_num(l, k)
    case (Neg(k), Pos(l)) => true
    case (Neg(k), zero_int()) => true
    case (Pos(k), Neg(l)) => false
    case (Pos(k), Pos(l)) => less_num(k, l)
    case (Pos(k), zero_int()) => false
    case (zero_int(), Neg(l)) => false
    case (zero_int(), Pos(l)) => true
    case (zero_int(), zero_int()) => false
  }

  def binary_expr(xa0: IRNode, x: Value, y: Value): Value = (xa0, x, y) match {
    case (AddNode(), IntVal(x), IntVal(y)) => IntVal(plus_int(x, y))
    case (SubNode(), IntVal(x), IntVal(y)) => IntVal(minus_int(x, y))
    case (MulNode(), IntVal(x), IntVal(y)) => IntVal(times_int(x, y))
    case (AndNode(), x, y) =>
      binary_bool_expr(AddNode(), val_to_bool(x), val_to_bool(y))
    case (OrNode(), x, y) =>
      binary_bool_expr(OrNode(), val_to_bool(x), val_to_bool(y))
    case (XorNode(), x, y) =>
      binary_bool_expr(XorNode(), val_to_bool(x), val_to_bool(y))
    case (IntegerLessThanNode(), IntVal(x), IntVal(y)) =>
      bool_to_val(less_int(x, y))
    case (IntegerEqualsNode(), IntVal(x), IntVal(y)) =>
      bool_to_val(equal_int(x, y))
    case (CallNode(), uv, uw) => UndefVal()
    case (ConstantNode(v), uv, uw) => UndefVal()
    case (ParameterNode(v), uv, uw) => UndefVal()
    case (PhiNode(), uv, uw) => UndefVal()
    case (SubNode(), UndefVal(), uw) => UndefVal()
    case (SubNode(), uv, UndefVal()) => UndefVal()
    case (MulNode(), UndefVal(), uw) => UndefVal()
    case (MulNode(), uv, UndefVal()) => UndefVal()
    case (SwitchNode(), uv, uw) => UndefVal()
    case (IfNode(), uv, uw) => UndefVal()
    case (ShortCircuitOrNode(v, va), uv, uw) => UndefVal()
    case (LogicNegationNode(), uv, uw) => UndefVal()
    case (KillingBeginNode(), uv, uw) => UndefVal()
    case (BeginNode(), uv, uw) => UndefVal()
    case (StartNode(), uv, uw) => UndefVal()
    case (LoopEndNode(), uv, uw) => UndefVal()
    case (MergeNode(), uv, uw) => UndefVal()
    case (ReturnNode(), uv, uw) => UndefVal()
    case (EndNode(), uv, uw) => UndefVal()
    case (LoopBeginNode(), uv, uw) => UndefVal()
    case (LoopExit(), uv, uw) => UndefVal()
    case (AbsNode(), uv, uw) => UndefVal()
    case (NegateNode(), uv, uw) => UndefVal()
    case (IntegerEqualsNode(), UndefVal(), uw) => UndefVal()
    case (IntegerEqualsNode(), uv, UndefVal()) => UndefVal()
    case (IntegerLessThanNode(), UndefVal(), uw) => UndefVal()
    case (IntegerLessThanNode(), uv, UndefVal()) => UndefVal()
    case (ConditionalNode(), uv, uw) => UndefVal()
    case (NewInstanceNode(v), uv, uw) => UndefVal()
    case (LoadFieldNode(v), uv, uw) => UndefVal()
    case (StoreFieldNode(v), uv, uw) => UndefVal()
    case (LoadStaticFieldNode(v, va), uv, uw) => UndefVal()
    case (StoreStaticFieldNode(v, va), uv, uw) => UndefVal()
    case (FrameStateNode(), uv, uw) => UndefVal()
    case (AddNode(), UndefVal(), uw) => UndefVal()
    case (AddNode(), uv, UndefVal()) => UndefVal()
  }

  def unary_expr(xa0: IRNode, x: Value): Value = (xa0, x) match {
    case (AbsNode(), IntVal(x)) =>
      IntVal((if (less_int(x, zero_int())) uminus_int(x) else x))
    case (NegateNode(), x) => bool_to_val(! (val_to_bool(x)))
    case (CallNode(), uv) => UndefVal()
    case (ConstantNode(v), uv) => UndefVal()
    case (ParameterNode(v), uv) => UndefVal()
    case (PhiNode(), uv) => UndefVal()
    case (AddNode(), uv) => UndefVal()
    case (SubNode(), uv) => UndefVal()
    case (MulNode(), uv) => UndefVal()
    case (SwitchNode(), uv) => UndefVal()
    case (IfNode(), uv) => UndefVal()
    case (ShortCircuitOrNode(v, va), uv) => UndefVal()
    case (LogicNegationNode(), uv) => UndefVal()
    case (KillingBeginNode(), uv) => UndefVal()
    case (BeginNode(), uv) => UndefVal()
    case (StartNode(), uv) => UndefVal()
    case (LoopEndNode(), uv) => UndefVal()
    case (MergeNode(), uv) => UndefVal()
    case (ReturnNode(), uv) => UndefVal()
    case (EndNode(), uv) => UndefVal()
    case (LoopBeginNode(), uv) => UndefVal()
    case (LoopExit(), uv) => UndefVal()
    case (AndNode(), uv) => UndefVal()
    case (OrNode(), uv) => UndefVal()
    case (XorNode(), uv) => UndefVal()
    case (IntegerEqualsNode(), uv) => UndefVal()
    case (IntegerLessThanNode(), uv) => UndefVal()
    case (ConditionalNode(), uv) => UndefVal()
    case (NewInstanceNode(v), uv) => UndefVal()
    case (LoadFieldNode(v), uv) => UndefVal()
    case (StoreFieldNode(v), uv) => UndefVal()
    case (LoadStaticFieldNode(v, va), uv) => UndefVal()
    case (StoreStaticFieldNode(v, va), uv) => UndefVal()
    case (FrameStateNode(), uv) => UndefVal()
    case (AbsNode(), UndefVal()) => UndefVal()
  }

  def s_graph(x0: EvalState): IRGraph = x0 match {
    case EvalStatea(x1, x2, x3, x4, x5, x6) => x1
  }

  def g_successors(x0: IRGraph): nat => List[nat] = x0 match {
    case Graph(x1, x2, x3, x4) => x4
  }

  def size_list[A]: (List[A]) => nat =
    ((a: List[A]) => gen_length[A](zero_nat(), a))

  def less_eq_nat(x0: nat, n: nat): Boolean = (x0, n) match {
    case (Suc(m), n) => less_nat(m, n)
    case (zero_nat(), n) => true
  }

  def less_nat(m: nat, x1: nat): Boolean = (m, x1) match {
    case (m, Suc(n)) => less_eq_nat(m, n)
    case (n, zero_nat()) => false
  }

  def g_usages(x0: IRGraph, n: nat): set[nat] = (x0, n) match {
    case (Graph(ids, nodes, inputs, successors), n) =>
      filter[nat](((i: nat) => member[nat](inputs(i), n)), ids)
  }

  def get_successor(n: nat, state: EvalState, i: nat): nat =
  {
    val g: IRGraph = s_graph(state);
    (if (less_nat(zero_nat(), size_list[nat].apply((g_successors(g)).apply(n))))
      nth[nat]((g_successors(g)).apply(n), i)
    else the_elem[nat](g_usages(g, n)))
  }

  def g_nodes(x0: IRGraph): nat => IRNode = x0 match {
    case Graph(x1, x2, x3, x4) => x2
  }

  def get_node(n: nat, state: EvalState): IRNode =
    (g_nodes(s_graph(state))).apply(n)

  def successori(nid: nat, state: EvalState, i: nat): (nat, (IRNode, EvalState)) =
  {
    val next_id: nat = get_successor(nid, state, i);
    (next_id, (get_node(next_id, state), state))
  }

  def one_nat: nat = Suc(zero_nat())

  def g_inputs(x0: IRGraph): nat => List[nat] = x0 match {
    case Graph(x1, x2, x3, x4) => x3
  }

  def get_input(nid: nat, state: EvalState, i: nat): nat =
    nth[nat]((g_inputs(s_graph(state))).apply(nid), i)

  def input(nid: nat, state: EvalState, i: nat): (nat, (IRNode, EvalState)) =
  {
    val next_id: nat = get_input(nid, state, i);
    (next_id, (get_node(next_id, state), state))
  }

  def eval_Piii_Poo(x0: (nat, (IRNode, EvalState))): pred[(EvalState, Value)] = x0
  match {
    case (xa, (xb, xc)) =>
      sup_pred[(EvalState,
        Value)](bind[(nat, (IRNode, EvalState)),
        (EvalState,
          Value)](single[(nat,
        (IRNode, EvalState))]((xa, (xb, xc))),
        ((a: (nat, (IRNode, EvalState))) =>
          (a match {
            case (_, (CallNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (ConstantNode(_), _)) => bot_pred[(EvalState, Value)]
            case (_, (ParameterNode(_), _)) => bot_pred[(EvalState, Value)]
            case (_, (PhiNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (AddNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (SubNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (MulNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (SwitchNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (IfNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (ShortCircuitOrNode(_, _), _)) => bot_pred[(EvalState, Value)]
            case (_, (LogicNegationNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (KillingBeginNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (BeginNode(), _)) => bot_pred[(EvalState, Value)]
            case (num, (StartNode(), s)) =>
              bind[(EvalState, Value),
                (EvalState,
                  Value)](eval_Piii_Poo(successori(num, s, zero_nat())),
                ((aa: (EvalState, Value)) =>
                {
                  val (x, y): (EvalState, Value) = aa;
                  single[(EvalState, Value)]((x, y))
                }))
            case (_, (LoopEndNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (MergeNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (ReturnNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (EndNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (LoopBeginNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (LoopExit(), _)) => bot_pred[(EvalState, Value)]
            case (_, (AbsNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (AndNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (OrNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (XorNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (NegateNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (IntegerEqualsNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (IntegerLessThanNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (ConditionalNode(), _)) => bot_pred[(EvalState, Value)]
            case (_, (NewInstanceNode(_), _)) => bot_pred[(EvalState, Value)]
            case (_, (LoadFieldNode(_), _)) => bot_pred[(EvalState, Value)]
            case (_, (StoreFieldNode(_), _)) => bot_pred[(EvalState, Value)]
            case (_, (LoadStaticFieldNode(_, _), _)) => bot_pred[(EvalState, Value)]
            case (_, (StoreStaticFieldNode(_, _), _)) => bot_pred[(EvalState, Value)]
            case (_, (FrameStateNode(), _)) => bot_pred[(EvalState, Value)]
          }))),
        sup_pred[(EvalState,
          Value)](bind[(nat, (IRNode, EvalState)),
          (EvalState,
            Value)](single[(nat, (IRNode, EvalState))]((xa, (xb, xc))),
          ((a: (nat, (IRNode, EvalState))) =>
          {
            val (num, (node, s)): (nat, (IRNode, EvalState)) = a;
            bind[Unit,
              (EvalState,
                Value)](if_pred(is_unary_node(node)),
              ((aa: Unit) =>
              {
                val (): Unit = aa;
                bind[(EvalState, Value),
                  (EvalState,
                    Value)](eval_Piii_Poo(input(num, s, zero_nat())),
                  ((ab: (EvalState, Value)) =>
                  {
                    val (s1, v1): (EvalState, Value) = ab;
                    single[(EvalState, Value)]((s1, unary_expr(node, v1)))
                  }))
              }))
          })),
          sup_pred[(EvalState,
            Value)](bind[(nat, (IRNode, EvalState)),
            (EvalState,
              Value)](single[(nat,
            (IRNode, EvalState))]((xa, (xb, xc))),
            ((a: (nat, (IRNode, EvalState))) =>
            {
              val (num, (node, s)): (nat, (IRNode, EvalState)) = a;
              bind[Unit,
                (EvalState,
                  Value)](if_pred(is_binary_node(node)),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  bind[(EvalState, Value),
                    (EvalState,
                      Value)](eval_Piii_Poo(input(num, s,
                    zero_nat())),
                    ((ab: (EvalState, Value)) =>
                    {
                      val (s1, v1): (EvalState, Value) = ab;
                      bind[(EvalState, Value),
                        (EvalState,
                          Value)](eval_Piii_Poo(input(num, s1, one_nat)),
                        ((ac: (EvalState, Value)) =>
                        {
                          val (s2, v2): (EvalState, Value) = ac;
                          single[(EvalState,
                            Value)]((s2, binary_expr(node, v1, v2)))
                        }))
                    }))
                }))
            })),
            sup_pred[(EvalState,
              Value)](bind[(nat, (IRNode, EvalState)),
              (EvalState,
                Value)](single[(nat, (IRNode, EvalState))]((xa, (xb, xc))),
              ((a: (nat, (IRNode, EvalState))) =>
                (a match {
                  case (_, (CallNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (ConstantNode(_), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (ParameterNode(_), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (PhiNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (AddNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (SubNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (MulNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (SwitchNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (num, (IfNode(), s)) =>
                    bind[(EvalState, Value),
                      (EvalState,
                        Value)](eval_Piii_Poo(input(num, s,
                      zero_nat())),
                      ((aa: (EvalState, Value)) =>
                      {
                        val (s1, v1): (EvalState, Value) = aa;
                        bind[Unit,
                          (EvalState,
                            Value)](if_pred(val_to_bool(v1)),
                          ((ab: Unit) =>
                          {
                            val (): Unit = ab;
                            bind[(EvalState, Value),
                              (EvalState,
                                Value)](eval_Piii_Poo(successori(num, s1,
                              zero_nat())),
                              ((ac: (EvalState, Value)) => {
                                val (x, y): (EvalState, Value) = ac;
                                single[(EvalState, Value)]((x, y))
                              }))
                          }))
                      }))
                  case (_, (ShortCircuitOrNode(_, _), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (LogicNegationNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (KillingBeginNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (BeginNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (StartNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (LoopEndNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (MergeNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (ReturnNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (EndNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (LoopBeginNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (LoopExit(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (AbsNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (AndNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (OrNode(), _)) => bot_pred[(EvalState, Value)]
                  case (_, (XorNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (NegateNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (IntegerEqualsNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (IntegerLessThanNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (ConditionalNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (NewInstanceNode(_), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (LoadFieldNode(_), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (StoreFieldNode(_), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (LoadStaticFieldNode(_, _), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (StoreStaticFieldNode(_, _), _)) =>
                    bot_pred[(EvalState, Value)]
                  case (_, (FrameStateNode(), _)) =>
                    bot_pred[(EvalState, Value)]
                }))),
              bind[(nat, (IRNode, EvalState)),
                (EvalState,
                  Value)](single[(nat, (IRNode, EvalState))]((xa, (xb, xc))),
                ((a: (nat, (IRNode, EvalState))) =>
                  (a match {
                    case (_, (CallNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (ConstantNode(_), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (ParameterNode(_), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (PhiNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (AddNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (SubNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (MulNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (SwitchNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (num, (IfNode(), s)) =>
                      bind[(EvalState, Value),
                        (EvalState,
                          Value)](eval_Piii_Poo(input(num, s,
                        zero_nat())),
                        ((aa: (EvalState, Value)) =>
                        {
                          val (s1, v1): (EvalState, Value) = aa;
                          bind[Unit,
                            (EvalState,
                              Value)](if_pred(! (val_to_bool(v1))),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              bind[(EvalState, Value),
                                (EvalState,
                                  Value)](eval_Piii_Poo(successori(num, s1,
                                one_nat)),
                                ((ac: (EvalState, Value)) => {
                                  val (x, y): (EvalState, Value) = ac;
                                  single[(EvalState, Value)]((x, y))
                                }))
                            }))
                        }))
                    case (_, (ShortCircuitOrNode(_, _), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (LogicNegationNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (KillingBeginNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (BeginNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (StartNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (LoopEndNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (MergeNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (ReturnNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (EndNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (LoopBeginNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (LoopExit(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (AbsNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (AndNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (OrNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (XorNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (NegateNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (IntegerEqualsNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (IntegerLessThanNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (ConditionalNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (NewInstanceNode(_), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (LoadFieldNode(_), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (StoreFieldNode(_), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (LoadStaticFieldNode(_, _), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (StoreStaticFieldNode(_, _), _)) =>
                      bot_pred[(EvalState, Value)]
                    case (_, (FrameStateNode(), _)) =>
                      bot_pred[(EvalState, Value)]
                  })))))))
  }

  def eval_Piii_Pio(x0: (nat, (IRNode, EvalState)), xd: EvalState): pred[Value] =
    (x0, xd) match {
      case ((xa, (xb, xc)), xd) =>
        sup_pred[Value](bind[((nat, (IRNode, EvalState)), EvalState),
          Value](single[((nat, (IRNode, EvalState)),
          EvalState)](((xa, (xb, xc)), xd)),
          ((a: ((nat, (IRNode, EvalState)), EvalState))
          =>
            (a match {
              case ((_, (CallNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (ConstantNode(_), _)), _) =>
                bot_pred[Value]
              case ((_, (ParameterNode(_), _)), _) =>
                bot_pred[Value]
              case ((_, (PhiNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (AddNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (SubNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (MulNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (SwitchNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (IfNode(), _)), _) =>
                bot_pred[Value]
              case
                ((_, (ShortCircuitOrNode(_, _), _)), _) => bot_pred[Value]
              case ((_, (LogicNegationNode(), _)), _)
              => bot_pred[Value]
              case ((_, (KillingBeginNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (BeginNode(), _)), _) =>
                bot_pred[Value]
              case ((num, (StartNode(), s)), x) =>
                bind[Value,
                  Value](eval_Piii_Pio(successori(num, s, zero_nat()), x),
                  ((aa: Value) => single[Value](aa)))
              case ((_, (LoopEndNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (MergeNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (ReturnNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (EndNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (LoopBeginNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (LoopExit(), _)), _) =>
                bot_pred[Value]
              case ((_, (AbsNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (AndNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (OrNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (XorNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (NegateNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (IntegerEqualsNode(), _)), _)
              => bot_pred[Value]
              case ((_, (IntegerLessThanNode(), _)), _)
              => bot_pred[Value]
              case ((_, (ConditionalNode(), _)), _) =>
                bot_pred[Value]
              case ((_, (NewInstanceNode(_), _)), _) =>
                bot_pred[Value]
              case ((_, (LoadFieldNode(_), _)), _) =>
                bot_pred[Value]
              case ((_, (StoreFieldNode(_), _)), _) =>
                bot_pred[Value]
              case
                ((_, (LoadStaticFieldNode(_, _), _)), _) => bot_pred[Value]
              case
                ((_, (StoreStaticFieldNode(_, _), _)), _) => bot_pred[Value]
              case ((_, (FrameStateNode(), _)), _) =>
                bot_pred[Value]
            }))),
          sup_pred[Value](bind[((nat, (IRNode, EvalState)),
            EvalState),
            Value](single[((nat, (IRNode, EvalState)), EvalState)](((xa, (xb, xc)), xd)),
            ((a: ((nat, (IRNode, EvalState)), EvalState)) =>
            {
              val ((num, (node, s)), s1):
                ((nat, (IRNode, EvalState)), EvalState)
              = a;
              bind[Unit,
                Value](if_pred(is_unary_node(node)),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  bind[Value,
                    Value](eval_Piii_Pio(input(num, s,
                    zero_nat()),
                    s1),
                    ((x: Value) => single[Value](unary_expr(node, x))))
                }))
            })),
            sup_pred[Value](bind[((nat,
              (IRNode, EvalState)),
              EvalState),
              Value](single[((nat, (IRNode, EvalState)),
              EvalState)](((xa, (xb, xc)), xd)),
              ((a: ((nat, (IRNode, EvalState)), EvalState)) =>
              {
                val ((num, (node, s)), s2):
                  ((nat, (IRNode, EvalState)), EvalState)
                = a;
                bind[Unit,
                  Value](if_pred(is_binary_node(node)),
                  ((aa: Unit) =>
                  {
                    val (): Unit = aa;
                    bind[(EvalState, Value),
                      Value](eval_Piii_Poo(input(num, s, zero_nat())),
                      ((ab: (EvalState, Value)) =>
                      {
                        val (s1, v1): (EvalState, Value) = ab;
                        bind[Value,
                          Value](eval_Piii_Pio(input(num, s1, one_nat),
                          s2),
                          ((x: Value) => single[Value](binary_expr(node, v1, x))))
                      }))
                  }))
              })),
              sup_pred[Value](bind[((nat, (IRNode, EvalState)), EvalState),
                Value](single[((nat, (IRNode, EvalState)),
                EvalState)](((xa, (xb, xc)), xd)),
                ((a: ((nat, (IRNode, EvalState)), EvalState)) =>
                  (a match {
                    case ((_, (CallNode(), _)), _) => bot_pred[Value]
                    case ((_, (ConstantNode(_), _)), _) => bot_pred[Value]
                    case ((_, (ParameterNode(_), _)), _) => bot_pred[Value]
                    case ((_, (PhiNode(), _)), _) => bot_pred[Value]
                    case ((_, (AddNode(), _)), _) => bot_pred[Value]
                    case ((_, (SubNode(), _)), _) => bot_pred[Value]
                    case ((_, (MulNode(), _)), _) => bot_pred[Value]
                    case ((_, (SwitchNode(), _)), _) => bot_pred[Value]
                    case ((num, (IfNode(), s)), x) =>
                      bind[(EvalState, Value),
                        Value](eval_Piii_Poo(input(num, s, zero_nat())),
                        ((aa: (EvalState, Value)) =>
                        {
                          val (s1, v1): (EvalState, Value) = aa;
                          bind[Unit,
                            Value](if_pred(val_to_bool(v1)),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              bind[Value,
                                Value](eval_Piii_Pio(successori(num, s1, zero_nat()), x),
                                ((ac: Value) => single[Value](ac)))
                            }))
                        }))
                    case ((_, (ShortCircuitOrNode(_, _), _)), _) => bot_pred[Value]
                    case ((_, (LogicNegationNode(), _)), _) => bot_pred[Value]
                    case ((_, (KillingBeginNode(), _)), _) => bot_pred[Value]
                    case ((_, (BeginNode(), _)), _) => bot_pred[Value]
                    case ((_, (StartNode(), _)), _) => bot_pred[Value]
                    case ((_, (LoopEndNode(), _)), _) => bot_pred[Value]
                    case ((_, (MergeNode(), _)), _) => bot_pred[Value]
                    case ((_, (ReturnNode(), _)), _) => bot_pred[Value]
                    case ((_, (EndNode(), _)), _) => bot_pred[Value]
                    case ((_, (LoopBeginNode(), _)), _) => bot_pred[Value]
                    case ((_, (LoopExit(), _)), _) => bot_pred[Value]
                    case ((_, (AbsNode(), _)), _) => bot_pred[Value]
                    case ((_, (AndNode(), _)), _) => bot_pred[Value]
                    case ((_, (OrNode(), _)), _) => bot_pred[Value]
                    case ((_, (XorNode(), _)), _) => bot_pred[Value]
                    case ((_, (NegateNode(), _)), _) => bot_pred[Value]
                    case ((_, (IntegerEqualsNode(), _)), _) => bot_pred[Value]
                    case ((_, (IntegerLessThanNode(), _)), _) => bot_pred[Value]
                    case ((_, (ConditionalNode(), _)), _) => bot_pred[Value]
                    case ((_, (NewInstanceNode(_), _)), _) => bot_pred[Value]
                    case ((_, (LoadFieldNode(_), _)), _) => bot_pred[Value]
                    case ((_, (StoreFieldNode(_), _)), _) => bot_pred[Value]
                    case ((_, (LoadStaticFieldNode(_, _), _)), _) => bot_pred[Value]
                    case ((_, (StoreStaticFieldNode(_, _), _)), _) => bot_pred[Value]
                    case ((_, (FrameStateNode(), _)), _) => bot_pred[Value]
                  }))),
                bind[((nat, (IRNode, EvalState)), EvalState),
                  Value](single[((nat, (IRNode, EvalState)),
                  EvalState)](((xa, (xb, xc)), xd)),
                  ((a: ((nat, (IRNode, EvalState)), EvalState)) =>
                    (a match {
                      case ((_, (CallNode(), _)), _) => bot_pred[Value]
                      case ((_, (ConstantNode(_), _)), _) => bot_pred[Value]
                      case ((_, (ParameterNode(_), _)), _) => bot_pred[Value]
                      case ((_, (PhiNode(), _)), _) => bot_pred[Value]
                      case ((_, (AddNode(), _)), _) => bot_pred[Value]
                      case ((_, (SubNode(), _)), _) => bot_pred[Value]
                      case ((_, (MulNode(), _)), _) => bot_pred[Value]
                      case ((_, (SwitchNode(), _)), _) => bot_pred[Value]
                      case ((num, (IfNode(), s)), x) =>
                        bind[(EvalState, Value),
                          Value](eval_Piii_Poo(input(num, s, zero_nat())),
                          ((aa: (EvalState, Value)) =>
                          {
                            val (s1, v1): (EvalState, Value) = aa;
                            bind[Unit,
                              Value](if_pred(! (val_to_bool(v1))),
                              ((ab: Unit) =>
                              {
                                val (): Unit = ab;
                                bind[Value,
                                  Value](eval_Piii_Pio(successori(num, s1, one_nat), x),
                                  ((ac: Value) => single[Value](ac)))
                              }))
                          }))
                      case ((_, (ShortCircuitOrNode(_, _), _)), _) => bot_pred[Value]
                      case ((_, (LogicNegationNode(), _)), _) => bot_pred[Value]
                      case ((_, (KillingBeginNode(), _)), _) => bot_pred[Value]
                      case ((_, (BeginNode(), _)), _) => bot_pred[Value]
                      case ((_, (StartNode(), _)), _) => bot_pred[Value]
                      case ((_, (LoopEndNode(), _)), _) => bot_pred[Value]
                      case ((_, (MergeNode(), _)), _) => bot_pred[Value]
                      case ((_, (ReturnNode(), _)), _) => bot_pred[Value]
                      case ((_, (EndNode(), _)), _) => bot_pred[Value]
                      case ((_, (LoopBeginNode(), _)), _) => bot_pred[Value]
                      case ((_, (LoopExit(), _)), _) => bot_pred[Value]
                      case ((_, (AbsNode(), _)), _) => bot_pred[Value]
                      case ((_, (AndNode(), _)), _) => bot_pred[Value]
                      case ((_, (OrNode(), _)), _) => bot_pred[Value]
                      case ((_, (XorNode(), _)), _) => bot_pred[Value]
                      case ((_, (NegateNode(), _)), _) => bot_pred[Value]
                      case ((_, (IntegerEqualsNode(), _)), _) => bot_pred[Value]
                      case ((_, (IntegerLessThanNode(), _)), _) => bot_pred[Value]
                      case ((_, (ConditionalNode(), _)), _) => bot_pred[Value]
                      case ((_, (NewInstanceNode(_), _)), _) => bot_pred[Value]
                      case ((_, (LoadFieldNode(_), _)), _) => bot_pred[Value]
                      case ((_, (StoreFieldNode(_), _)), _) => bot_pred[Value]
                      case ((_, (LoadStaticFieldNode(_, _), _)), _) => bot_pred[Value]
                      case ((_, (StoreStaticFieldNode(_, _), _)), _) => bot_pred[Value]
                      case ((_, (FrameStateNode(), _)), _) => bot_pred[Value]
                    })))))))
    }

  def eval_Piii_Pii(x0: (nat, (IRNode, EvalState)), x1: (EvalState, Value)):
  pred[Unit]
  =
    (x0, x1) match {
      case ((xa, (xb, xc)), (xd, xe)) =>
        sup_pred[Unit](bind[((nat, (IRNode, EvalState)), (EvalState, Value)),
          Unit](single[((nat, (IRNode, EvalState)),
          (EvalState, Value))](((xa, (xb, xc)), (xd, xe))),
          ((a: ((nat, (IRNode, EvalState)),
            (EvalState, Value)))
          =>
            (a match {
              case ((_, (CallNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (ConstantNode(_), _)), _) =>
                bot_pred[Unit]
              case ((_, (ParameterNode(_), _)), _) =>
                bot_pred[Unit]
              case ((_, (PhiNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (AddNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (SubNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (MulNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (SwitchNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (IfNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (ShortCircuitOrNode(_, _), _)),
              _)
              => bot_pred[Unit]
              case ((_, (LogicNegationNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (KillingBeginNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (BeginNode(), _)), _) =>
                bot_pred[Unit]
              case ((num, (StartNode(), s)), (x, y)) =>
                bind[Unit,
                  Unit](eval_Piii_Pii(successori(num, s, zero_nat()), (x, y)),
                  ((aa: Unit) => {
                    val (): Unit = aa;
                    single[Unit](())
                  }))
              case ((_, (LoopEndNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (MergeNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (ReturnNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (EndNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (LoopBeginNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (LoopExit(), _)), _) =>
                bot_pred[Unit]
              case ((_, (AbsNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (AndNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (OrNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (XorNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (NegateNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (IntegerEqualsNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (IntegerLessThanNode(), _)), _)
              => bot_pred[Unit]
              case ((_, (ConditionalNode(), _)), _) =>
                bot_pred[Unit]
              case ((_, (NewInstanceNode(_), _)), _) =>
                bot_pred[Unit]
              case ((_, (LoadFieldNode(_), _)), _) =>
                bot_pred[Unit]
              case ((_, (StoreFieldNode(_), _)), _) =>
                bot_pred[Unit]
              case ((_, (LoadStaticFieldNode(_, _), _)),
              _)
              => bot_pred[Unit]
              case ((_, (StoreStaticFieldNode(_, _), _)),
              _)
              => bot_pred[Unit]
              case ((_, (FrameStateNode(), _)), _) =>
                bot_pred[Unit]
            }))),
          sup_pred[Unit](bind[((nat, (IRNode, EvalState)),
            (EvalState, Value)),
            Unit](single[((nat, (IRNode, EvalState)),
            (EvalState, Value))](((xa, (xb, xc)), (xd, xe))),
            ((a: ((nat, (IRNode, EvalState)), (EvalState, Value))) =>
            {
              val ((num, (node, s)), (s1, xaa)):
                ((nat, (IRNode, EvalState)), (EvalState, Value))
              = a;
              bind[Unit,
                Unit](if_pred(is_unary_node(node)),
                ((aa: Unit) =>
                {
                  val (): Unit = aa;
                  bind[Value,
                    Unit](eval_Piii_Pio(input(num, s,
                    zero_nat()),
                    s1),
                    ((x: Value) =>
                      (if (equal_Value(xaa, unary_expr(node, x))) single[Unit](())
                      else bot_pred[Unit])))
                }))
            })),
            sup_pred[Unit](bind[((nat,
              (IRNode, EvalState)),
              (EvalState, Value)),
              Unit](single[((nat, (IRNode, EvalState)),
              (EvalState,
                Value))](((xa, (xb, xc)), (xd, xe))),
              ((a: ((nat, (IRNode, EvalState)), (EvalState, Value)))
              =>
              {
                val ((num, (node, s)), (s2, xaa)):
                  ((nat, (IRNode, EvalState)),
                    (EvalState, Value))
                = a;
                bind[Unit,
                  Unit](if_pred(is_binary_node(node)),
                  ((aa: Unit) =>
                  {
                    val (): Unit = aa;
                    bind[(EvalState, Value),
                      Unit](eval_Piii_Poo(input(num, s, zero_nat())),
                      ((ab: (EvalState, Value)) =>
                      {
                        val (s1, v1): (EvalState, Value) = ab;
                        bind[Value,
                          Unit](eval_Piii_Pio(input(num, s1, one_nat), s2),
                          ((x: Value) =>
                            (if (equal_Value(xaa,
                              binary_expr(node, v1, x)))
                              single[Unit](()) else bot_pred[Unit])))
                      }))
                  }))
              })),
              sup_pred[Unit](bind[((nat, (IRNode, EvalState)),
                (EvalState, Value)),
                Unit](single[((nat, (IRNode, EvalState)),
                (EvalState, Value))](((xa, (xb, xc)), (xd, xe))),
                ((a: ((nat, (IRNode, EvalState)), (EvalState, Value))) =>
                  (a match {
                    case ((_, (CallNode(), _)), _) => bot_pred[Unit]
                    case ((_, (ConstantNode(_), _)), _) => bot_pred[Unit]
                    case ((_, (ParameterNode(_), _)), _) => bot_pred[Unit]
                    case ((_, (PhiNode(), _)), _) => bot_pred[Unit]
                    case ((_, (AddNode(), _)), _) => bot_pred[Unit]
                    case ((_, (SubNode(), _)), _) => bot_pred[Unit]
                    case ((_, (MulNode(), _)), _) => bot_pred[Unit]
                    case ((_, (SwitchNode(), _)), _) => bot_pred[Unit]
                    case ((num, (IfNode(), s)), (x, y)) =>
                      bind[(EvalState, Value),
                        Unit](eval_Piii_Poo(input(num, s, zero_nat())),
                        ((aa: (EvalState, Value)) =>
                        {
                          val (s1, v1): (EvalState, Value) = aa;
                          bind[Unit,
                            Unit](eval_Piii_Pii(successori(num, s1,
                            zero_nat()),
                            (x, y)),
                            ((ab: Unit) =>
                            {
                              val (): Unit = ab;
                              bind[Unit,
                                Unit](if_pred(val_to_bool(v1)), ((ac: Unit) => {
                                val (): Unit = ac;
                                single[Unit](())
                              }))
                            }))
                        }))
                    case ((_, (ShortCircuitOrNode(_, _), _)), _) => bot_pred[Unit]
                    case ((_, (LogicNegationNode(), _)), _) => bot_pred[Unit]
                    case ((_, (KillingBeginNode(), _)), _) => bot_pred[Unit]
                    case ((_, (BeginNode(), _)), _) => bot_pred[Unit]
                    case ((_, (StartNode(), _)), _) => bot_pred[Unit]
                    case ((_, (LoopEndNode(), _)), _) => bot_pred[Unit]
                    case ((_, (MergeNode(), _)), _) => bot_pred[Unit]
                    case ((_, (ReturnNode(), _)), _) => bot_pred[Unit]
                    case ((_, (EndNode(), _)), _) => bot_pred[Unit]
                    case ((_, (LoopBeginNode(), _)), _) => bot_pred[Unit]
                    case ((_, (LoopExit(), _)), _) => bot_pred[Unit]
                    case ((_, (AbsNode(), _)), _) => bot_pred[Unit]
                    case ((_, (AndNode(), _)), _) => bot_pred[Unit]
                    case ((_, (OrNode(), _)), _) => bot_pred[Unit]
                    case ((_, (XorNode(), _)), _) => bot_pred[Unit]
                    case ((_, (NegateNode(), _)), _) => bot_pred[Unit]
                    case ((_, (IntegerEqualsNode(), _)), _) => bot_pred[Unit]
                    case ((_, (IntegerLessThanNode(), _)), _) => bot_pred[Unit]
                    case ((_, (ConditionalNode(), _)), _) => bot_pred[Unit]
                    case ((_, (NewInstanceNode(_), _)), _) => bot_pred[Unit]
                    case ((_, (LoadFieldNode(_), _)), _) => bot_pred[Unit]
                    case ((_, (StoreFieldNode(_), _)), _) => bot_pred[Unit]
                    case ((_, (LoadStaticFieldNode(_, _), _)), _) => bot_pred[Unit]
                    case ((_, (StoreStaticFieldNode(_, _), _)), _) => bot_pred[Unit]
                    case ((_, (FrameStateNode(), _)), _) => bot_pred[Unit]
                  }))),
                bind[((nat, (IRNode, EvalState)),
                  (EvalState, Value)),
                  Unit](single[((nat, (IRNode, EvalState)),
                  (EvalState, Value))](((xa, (xb, xc)), (xd, xe))),
                  ((a: ((nat, (IRNode, EvalState)), (EvalState, Value))) =>
                    (a match {
                      case ((_, (CallNode(), _)), _) => bot_pred[Unit]
                      case ((_, (ConstantNode(_), _)), _) => bot_pred[Unit]
                      case ((_, (ParameterNode(_), _)), _) => bot_pred[Unit]
                      case ((_, (PhiNode(), _)), _) => bot_pred[Unit]
                      case ((_, (AddNode(), _)), _) => bot_pred[Unit]
                      case ((_, (SubNode(), _)), _) => bot_pred[Unit]
                      case ((_, (MulNode(), _)), _) => bot_pred[Unit]
                      case ((_, (SwitchNode(), _)), _) => bot_pred[Unit]
                      case ((num, (IfNode(), s)), (x, y)) =>
                        bind[(EvalState, Value),
                          Unit](eval_Piii_Poo(input(num, s, zero_nat())),
                          ((aa: (EvalState, Value)) =>
                          {
                            val (s1, v1): (EvalState, Value) = aa;
                            bind[Unit,
                              Unit](eval_Piii_Pii(successori(num, s1, one_nat),
                              (x, y)),
                              ((ab: Unit) =>
                              {
                                val (): Unit = ab;
                                bind[Unit,
                                  Unit](if_pred(! (val_to_bool(v1))),
                                  ((ac: Unit) => {
                                    val (): Unit = ac;
                                    single[Unit](())
                                  }))
                              }))
                          }))
                      case ((_, (ShortCircuitOrNode(_, _), _)), _) => bot_pred[Unit]
                      case ((_, (LogicNegationNode(), _)), _) => bot_pred[Unit]
                      case ((_, (KillingBeginNode(), _)), _) => bot_pred[Unit]
                      case ((_, (BeginNode(), _)), _) => bot_pred[Unit]
                      case ((_, (StartNode(), _)), _) => bot_pred[Unit]
                      case ((_, (LoopEndNode(), _)), _) => bot_pred[Unit]
                      case ((_, (MergeNode(), _)), _) => bot_pred[Unit]
                      case ((_, (ReturnNode(), _)), _) => bot_pred[Unit]
                      case ((_, (EndNode(), _)), _) => bot_pred[Unit]
                      case ((_, (LoopBeginNode(), _)), _) => bot_pred[Unit]
                      case ((_, (LoopExit(), _)), _) => bot_pred[Unit]
                      case ((_, (AbsNode(), _)), _) => bot_pred[Unit]
                      case ((_, (AndNode(), _)), _) => bot_pred[Unit]
                      case ((_, (OrNode(), _)), _) => bot_pred[Unit]
                      case ((_, (XorNode(), _)), _) => bot_pred[Unit]
                      case ((_, (NegateNode(), _)), _) => bot_pred[Unit]
                      case ((_, (IntegerEqualsNode(), _)), _) => bot_pred[Unit]
                      case ((_, (IntegerLessThanNode(), _)), _) => bot_pred[Unit]
                      case ((_, (ConditionalNode(), _)), _) => bot_pred[Unit]
                      case ((_, (NewInstanceNode(_), _)), _) => bot_pred[Unit]
                      case ((_, (LoadFieldNode(_), _)), _) => bot_pred[Unit]
                      case ((_, (StoreFieldNode(_), _)), _) => bot_pred[Unit]
                      case ((_, (LoadStaticFieldNode(_, _), _)), _) => bot_pred[Unit]
                      case ((_, (StoreStaticFieldNode(_, _), _)), _) => bot_pred[Unit]
                      case ((_, (FrameStateNode(), _)), _) => bot_pred[Unit]
                    })))))))
    }

  def evala(x1: (nat, (IRNode, EvalState)), x2: (EvalState, Value)): Boolean =
    holds(eval_Piii_Pii(x1, x2))

  def main(args: Array[String]) = {
    val evalState : EvalState = EvalStatea(
      null,
      null,
      null,
      null,
      null,
      null
    )
//    evala();
  }

} /* object Compiler */
