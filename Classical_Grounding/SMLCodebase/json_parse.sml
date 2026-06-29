(* Minimal JSON parser -- just enough for Nemo's proof-trace output
   ({"finalConclusion": [...], "inferences": [{"conclusion": str,
     "premises": [str, ...], ...}, ...]}).

   Built on the SMLParsecomb (parcom) combinators, in the same style as the
   PDDL parser (planning/pddlParser/pddl_refactor.sml). *)

structure JsonParse :
sig
  datatype json =
      JObj of (string * json) list
    | JArr of json list
    | JStr of string
    | JNum of string        (* kept as raw text; never needed numerically *)
    | JBool of bool
    | JNull

  exception JsonError of string

  val parse : string -> json
  (* field lookup helpers *)
  val getField : json * string -> json option
  val getArr : json -> json list
  val getStr : json -> string
end =
struct
  datatype json =
      JObj of (string * json) list
    | JArr of json list
    | JStr of string
    | JNum of string
    | JBool of bool
    | JNull

  exception JsonError of string

  local
    open ParserCombinators
    open CharParser

    infixr 4 << >>
    infixr 3 &&
    infix  2 -- ##
    infix  2 wth suchthat return guard when
    infixr 1 || <|> ??

    (* lexeme: parser followed by optional whitespace *)
    fun tok p = p << spaces
    fun sym c = tok (char c)

    (* JSON string literal *)
    val escapedChar =
      char #"\\" >>
        (   char #"n" return #"\n"
        ||  char #"t" return #"\t"
        ||  char #"r" return #"\r"
        ||  char #"u" >> repeatn 4 hexDigit return #"?"  (* code points unused *)
        ||  anyChar                                       (* \" \\ \/ ... *)
        )
    val stringChar = escapedChar || noneOf [#"\"", #"\\"]
    val jstring : string charParser =
      tok (middle (char #"\"") (repeat stringChar) (char #"\"")) wth String.implode

    (* number, kept as raw text *)
    val numChar = satisfy (fn c => Char.isDigit c orelse c = #"-" orelse c = #"+"
                                   orelse c = #"." orelse c = #"e" orelse c = #"E")
    val jnumber = tok (repeat1 numChar) wth String.implode

    fun jvalue () : json charParser =
          jstring wth JStr
      ||  jnumber wth JNum
      ||  tok (string "true") return JBool true
      ||  tok (string "false") return JBool false
      ||  tok (string "null") return JNull
      ||  sym #"[" >> separate ($ jvalue) (sym #",") << sym #"]" wth JArr
      ||  sym #"{" >> separate ($ jfield) (sym #",") << sym #"}" wth JObj
    and jfield () : (string * json) charParser =
          jstring << sym #":" && $ jvalue

    val document = spaces >> $ jvalue
  in
    fun parse s =
      case CharParser.parseString document s of
        Sum.INR v => v
      | Sum.INL err => raise JsonError err
  end

  fun getField (JObj fields, k) =
        (case List.find (fn (k', _) => k' = k) fields of
           SOME (_, v) => SOME v
         | NONE => NONE)
    | getField (_, _) = NONE

  fun getArr (JArr xs) = xs
    | getArr _ = raise JsonError "expected array"

  fun getStr (JStr s) = s
    | getStr _ = raise JsonError "expected string"
end
