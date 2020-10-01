structure Elaborate : sig
              val elaborate : Ast.exp -> Ast.exp
          end =
struct
fun elaborate ast =
    let
        val datatypeNameToType = HashTable.mkTable (HashString.hashString, op=) (42, Fail "not found");
    in
        ast
    end
end
