signature NAMES =
sig
    val add : string -> unit
    val pop : unit -> unit
    val find : string -> int option
end

structure Names :> NAMES =
struct
    val names : string list ref = ref []
    fun add name = names := name::(!names)
    fun pop () = names := tl (!names)
    fun find name =
        case List.findi (fn (_, n) => n = name) (!names)
         of NONE => NONE
          | SOME (i, _) => SOME i
end
