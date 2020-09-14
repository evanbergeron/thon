(* Largely from "purely functional data structures" *)
signature Stack =
sig
    type ''a Stack
    val empty : ''a Stack
    val isEmpty : ''a Stack -> bool
    val cons : ''a * ''a Stack -> ''a Stack
    val head : ''a Stack -> ''a
    val tail : ''a Stack -> ''a Stack
    val findIdx : ''a * ''a Stack -> int
end

structure List :> Stack =
struct 
    type ''a Stack = ''a list
    val empty = []
    fun cons (x, xs) = x :: xs
    fun isEmpty xs = null xs
    fun head xs = hd xs;
    fun tail xs = tl xs;
    fun findIdx (x : ''a, xs : ''a Stack) =
        if isEmpty xs then raise Empty
        else if (x = (head xs)) then 0
        else 1 + (findIdx (x, tail xs))
end
         
