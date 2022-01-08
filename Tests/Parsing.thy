theory Parsing
  imports Graph.IRGraph
  keywords
    "graph" :: thy_decl and
    "graph_file" :: thy_load
begin
    
(*ML_file \<open>~~/src/Pure/General/input.ML\<close>*)
(*ML_file \<open>~~/src/Pure/General/scan.ML\<close>*)
(*ML_file \<open>~~/src/Pure/Isar/parse.ML\<close>*)
ML_file \<open>~~/src/Pure/Tools/rail.ML\<close>
                          
ML \<open>
fun print_line (node:string) =
  let
    (*val _ = @{print} nid;*)
    val _ = @{print} node;
  in
    ()
  end

datatype kind = 
  Nid of int |
  Colon |
  Space |
  Node of string

datatype token = Token of Position.range * (kind * string);

fun token k ss = [Token (Symbol_Pos.range ss, (k, Symbol_Pos.content ss))];

val scan_space = Scan.many1 (Symbol.is_blank o Symbol_Pos.symbol);

fun is_any char = Symbol.is_ascii char

val scan_any = Scan.many1 (is_any o Symbol_Pos.symbol);

val scan_digit = Scan.many1 (Symbol.is_digit o Symbol_Pos.symbol);
                        
val scan_colon = Scan.many1 ((fn str => str = ":") o Symbol_Pos.symbol);

val parse_nat = fst o Library.read_int o Symbol.explode;

val scan_token =
  scan_digit >> (fn ss => token (Nid (parse_nat (Symbol_Pos.content ss))) ss) ||
  scan_colon >> token Colon ||
  scan_space >> token Space ||
  scan_any >> (fn ss => token (Node (Symbol_Pos.content ss)) ss)

val scan =
  Scan.repeat scan_token;

val tokenize = #1 o Scan.error (Scan.finite Symbol_Pos.stopper scan);

(*
fun split_line (line: string) =
  (Scan.single (Parse.int -- Parse.term)) (Token.tokenize Keyword.empty_keywords {strict=false} (Symbol_Pos.explode0 line)) (*|-- Parse.int --| Parse.reserved ":" -- Parse.string*)
*)

fun read_tokens (tokens: token list) ctxt =
  let
    val nid = hd tokens;
    val nid_number = (case nid of Token (_, (Nid x, _)) => x | _ => 0);
    val node = hd (tl (tl (tl tokens)));
    val node_string = (case node of Token (_, (Node x, _)) => x | _ => "");
    val term = Syntax.read_term ctxt node_string;
  in
    (nid_number, term)
  end

fun split_line (line: Input.source) ctxt =
  let
    val toks = tokenize (Input.source_explode line);
    val toks = List.foldr op@ [] toks;
    val parsed = read_tokens toks ctxt;
  (*
    val scanned = (Parse.int -- Parse.$$$ ":" -- Parse.string) toks;
    val _ = @{print} scanned; *)
  in
    parsed
  end
                                                 
fun read_lines (lines:string list) ctxt =
  let
    val lines = filter (fn line => line <> "") lines;
    (*val lines = map (fn line => (line ^ (Char.toString (Char.chr (~1))))) lines;
    val _ = @{print} lines;*)
    (*val lines = map (fn line => split_line line) lines;*)
    val lines = map Input.string lines;
    (*val _ = @{print} lines;*)
    val lines = map (fn line => split_line line ctxt) lines;
    val _ = @{print} lines;
  in
    lines
  end

fun symbols_to_lines (start:string) (symbols:Symbol_Pos.T list) =
  case symbols of
    [] => [] |
    (("\n", _) :: xs) => start :: symbols_to_lines "" xs |
    ((chr, _) :: xs) => symbols_to_lines (start ^ chr) xs

fun record_definition (name: binding) (lines: string list) thy =
  let
    val trm = "[]";
    val t = Syntax.read_term thy trm;
    
    val ((_, (_, def)), lthy') = Local_Theory.define ((name, NoSyn), ((Thm.def_binding name, []), t)) thy;
    val lthy'' = Code.declare_default_eqns [(def, true)] lthy';
  in
    lthy''
  end

fun test name lines state =
  let
    val _ = read_lines lines (Toplevel.context_of state);
    val state' = record_definition name [] (Toplevel.context_of state);
  in
    state'
  end



fun parse (name: binding, args:Input.source) thy =
  let
    (*val state = Toplevel.theory_toplevel thy;*)
    val lines = (symbols_to_lines "" (Input.source_explode args));
    val _ = read_lines lines;
    (*val update = (test name lines) state;*)
  in
    ()
    (*Local_Theory.background_theory thy*)
     (*Toplevel.local_theory NONE NONE (test name lines) state*)
  end

fun open_and_parse (files:(theory -> Token.file list * theory)) thy =
  let
    val state = Toplevel.theory_toplevel thy;
    val thy = Toplevel.theory_of state;
    val many_lines = map (#lines) (fst (files thy));
    val lines = List.foldr op@ [] many_lines;
    val _ = read_lines lines (Toplevel.context_of state);
  in
    thy
  end

val _ = Outer_Syntax.command \<^command_keyword>\<open>graph\<close> "test"
   (Parse.binding -- Parse.document_source >> (Toplevel.keep o parse))


val _ = Outer_Syntax.command \<^command_keyword>\<open>graph_file\<close> "test"
   ((Resources.provide_parse_files (Command_Span.extensions ["graph"])) 
      >> (Toplevel.theory o open_and_parse))
\<close>

graph test1 \<open>
0: (StartNode (Some 2) 11, VoidStamp)
\<close>


graph test2 \<open>
0: (StartNode (Some 2) 11, VoidStamp)
1: (ParameterNode 0, IntegerStamp 32 (-2147483648) (2147483647))
2: (FrameState [] None None None, IllegalStamp)
3: (ConstantNode (IntVal32 (3)), IntegerStamp 32 (3) (3))
4: (ConstantNode (IntVal32 (4)), IntegerStamp 32 (4) (4))
5: (IntegerLessThanNode 1 4, VoidStamp)
6: (ConstantNode (IntVal32 (0)), IntegerStamp 32 (0) (0))
7: (ConstantNode (IntVal32 (1)), IntegerStamp 32 (1) (1))
8: (ConditionalNode 5 6 7, IntegerStamp 32 (0) (1))
9: (BeginNode 12, VoidStamp)
10: (BeginNode 13, VoidStamp)
11: (IfNode 5 10 9, VoidStamp)
12: (ReturnNode (Some 7) None, VoidStamp)
13: (ReturnNode (Some 7) None, VoidStamp)
\<close>


text \<open>\<close>

(*
0: (StartNode (Some 2) 11), VoidStamp)
1: (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647))
2: (FrameState [] None None None), IllegalStamp)
3: (ConstantNode (IntVal32 (3))), IntegerStamp 32 (3) (3))
4: (ConstantNode (IntVal32 (4))), IntegerStamp 32 (4) (4))
5: (IntegerLessThanNode 1 4), VoidStamp)
6: (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0))
7: (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1))
8: (ConditionalNode 5 6 7), IntegerStamp 32 (0) (1))
9: (BeginNode 12), VoidStamp)
10: (BeginNode 13), VoidStamp)
11: (IfNode 5 10 9), VoidStamp)
12: (ReturnNode (Some 7) None), VoidStamp)
13: (ReturnNode (Some 7) None), VoidStamp)
\<close>*)

graph_file \<open>test.graph\<close>

end